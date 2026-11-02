"""Fold small modules into the one module that imports them.

A module that exactly one file imports cannot be used by anything else, so its
body can be moved to the end of that importer: the importer keeps its name, the
merged module disappears, and every other file that saw the declarations
through the importer still sees them. The importer's import list becomes the
union of the two lists (minus the merged module), so the merged module's own
dependencies stay reachable.

    python3 scripts/MergeModules.py --dry --max-lines 100 NavierStokes
    python3 scripts/MergeModules.py --max-lines 100 --keep cite.txt NavierStokes

`--keep FILE` lists module names (one per line, with or without the directory
prefix) that must not be merged away -- the paper names files, and a file it
names has to keep existing. `--max-lines` bounds the size of what is moved.

The iteration repeats until nothing more can be merged, because a merge can
leave another module with a single importer.
"""
import collections
import os
import re
import sys

IMPORT = re.compile(r'^import\s+(\S+)')


def module_name(path):
    return path[:-5].replace(os.sep, '.')


SKIP = {'.lake', '.scratch', '.git', '.skill', '.ultramath'}


def lean_files(root='.'):
    """Every .lean file under `root`, skipping build and scratch directories."""
    out = []
    for dp, dns, fs in os.walk(root):
        dns[:] = [d for d in dns if d not in SKIP]
        out += [os.path.normpath(os.path.join(dp, f)) for f in fs if f.endswith('.lean')]
    return sorted(out)


def read(path):
    with open(path, errors='replace') as fh:
        return fh.read().split('\n')


SCOT = re.compile(r'^(?:variable|open|set_option|local|attribute|notation|scoped|'
                  r'noncomputable section|macro|syntax|elab|binder_predicate)\b')


def selfcontained(lines):
    """True when appending `lines` cannot change the elaboration of a file it is
    appended to, and appending to it cannot change `lines`: no `variable`, `open`,
    `set_option`, `local`, `attribute`, `notation` at file scope, i.e. outside a
    `section` (a `namespace` does not end the scope of a `variable`)."""
    section = 0
    for l in lines:
        t = l.strip()
        if not t or t.startswith('--') or t.startswith('/-') or t.endswith('-/'):
            continue
        if re.match(r'^section\b', t):
            section += 1
            continue
        if re.match(r'^end\b', t):
            section = max(section - 1, 0)
            continue
        if section == 0 and SCOT.match(t) and not t.endswith(' in'):
            return False
    return True


def body_start(lines):
    """Index of the first line after the last `import` line."""
    last = max((i for i, l in enumerate(lines) if IMPORT.match(l)), default=-1)
    return last + 1


def insert_at(lines):
    """Where a merged module goes: after the imports and after a leading module
    docstring, so that the parent keeps its own header at the top."""
    i = body_start(lines)
    n = len(lines)
    while i < n and not lines[i].strip():
        i += 1
    if i < n and lines[i].lstrip().startswith('/-'):
        while i < n and not lines[i].strip().endswith('-/'):
            i += 1
        i += 1
    return i


def main(argv):
    dry = '--dry' in argv
    clean = '--clean' in argv
    argv = [a for a in argv if a != '--clean']
    max_lines = 10 ** 6
    if '--max-lines' in argv:
        max_lines = int(argv[argv.index('--max-lines') + 1])
        del argv[argv.index('--max-lines'):argv.index('--max-lines') + 2]
    keep = set()
    while '--keep' in argv:
        k = argv.index('--keep')
        for l in open(argv[k + 1]):
            l = l.strip()
            if l and not l.startswith('#'):
                keep.add(l)
                keep.add(l.split('.')[-1])
        del argv[k:k + 2]
    root = [a for a in argv if not a.startswith('--')][0]

    total = 0
    inside = set(lean_files(root)) if root != '.' else None
    for it in range(1, 60):
        # the import graph is built over the whole repository: a module imported
        # by the umbrella file or by a script outside `root` is not free to move
        files = lean_files('.')
        byname = {module_name(p): p for p in files}
        texts = {p: read(p) for p in files}
        importers = collections.defaultdict(list)
        for p in files:
            for l in texts[p]:
                m = IMPORT.match(l)
                if m and m.group(1) in byname and m.group(1) != module_name(p):
                    importers[m.group(1)].append(p)
        if inside is None:
            inside = set(files)
        else:
            inside = {p for p in inside if os.path.exists(p)}

        merged_now = 0
        for name, p in sorted(byname.items(), key=lambda kv: len(texts[kv[1]])):
            if p not in inside:
                continue
            if name in keep or name.split('.')[-1] in keep:
                continue
            imps = importers.get(name, [])
            if len(imps) != 1:
                continue
            parent = imps[0]
            if parent not in inside or len(texts[p]) > max_lines:
                continue
            # `importers` is a snapshot of the pass. A parent merged away earlier
            # in the same pass no longer exists, and writing to it would recreate
            # a module nothing imports and lose its declarations.
            if not os.path.exists(parent) or not os.path.exists(p):
                continue
            if clean and not (selfcontained(texts[p]) and selfcontained(texts[parent])):
                continue
            plines = texts[parent]
            child = texts[p]
            # `import <name>` is replaced, *in place*, by the child's own imports:
            # that keeps the depth-first import order exactly as it was when the
            # parent imported the child, so instance resolution picks the same
            # (definitionally equal, but syntactically different) instance terms
            # and every declaration's type comes out byte-identical.
            new_parent = []
            for l in plines:
                m = IMPORT.match(l)
                if m and m.group(1) == name:
                    new_parent += ['import ' + IMPORT.match(c).group(1)
                                   for c in child if IMPORT.match(c)]
                else:
                    new_parent.append(l)
            seen, dedup = set(), []
            for l in new_parent:
                m = IMPORT.match(l)
                if m:
                    if m.group(1) in seen:
                        continue
                    seen.add(m.group(1))
                dedup.append(l)
            new_parent = dedup
            # The child's body goes *before* the parent's body, because `import`
            # elaborates the imported module first: that is the order the parent's
            # proofs were written against. It is wrapped in `section ... end`
            # because `open`, `variable` and `set_option` are section-scoped in
            # Lean 4, so the moved text cannot change the parent's elaboration
            # and the parent's header cannot change the moved text's.
            marker = (f'/-! Merged from `{name}`. The body is wrapped in a section so '
                      f'that its `open`s cannot leak into this file. -/')
            at = insert_at(new_parent)
            merged = (new_parent[:at] + ['', marker, 'section']
                      + child[body_start(child):] + ['', 'end', ''] + new_parent[at:])
            if not dry:
                with open(parent, 'w') as fh:
                    fh.write('\n'.join(merged))
                os.remove(p)
            merged_now += 1
            if not dry:
                byname.pop(name, None)
                texts[parent] = merged
        print(f'pass {it}: merged {merged_now}')
        total += merged_now
        if merged_now == 0 or dry:
            break
    print(f'total merged: {total}; files now: {len(lean_files(root))}')


if __name__ == '__main__':
    main(sys.argv[1:])
