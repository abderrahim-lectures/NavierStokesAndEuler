"""Delete `theorem`/`lemma` declarations that nothing in `NavierStokes/` refers to,
iterating to a fixed point, and clean up prefix blocks left without a command.

A declaration's span includes everything that belongs to it syntactically: a
preceding `omit ... in` / `include ... in` / `variable ... in` prefix (which may
be spread over several lines), an `@[...]` attribute line, and the docstring
block.  It ends just before the next top-level command.

One pass is not enough: deleting a lemma can remove the last reference to
another, so the passes repeat until nothing more is deleted.  A multi-line
prefix that survived a deletion is removed by `orphans`, which finds a prefix
block whose next command is `end` or nothing at all.

    python3 PruneUnusedLemmas.py --dry   NavierStokes     # report only
    python3 PruneUnusedLemmas.py --keep names.txt NavierStokes

`--keep FILE` protects one declaration name per line: the paper cites theorems
by name and they must survive even when nothing in the library uses them.
    python3 PruneUnusedLemmas.py         NavierStokes     # rewrite the files
"""
import collections
import os
import re
import sys

# `instance` is deliberately absent: an instance is used by *typeclass search*, not
# by its name, so a name count cannot see its uses. `structure`/`class`/`inductive`
# are absent for the same kind of reason (constructors, recursors, projections).
KINDS = 'theorem|lemma|def|abbrev'
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                  r"(" + KINDS + r")\s+([A-Za-z_][A-Za-z0-9_']*)")
# anything that starts a new top-level command at column 0
TOP = re.compile(r"^(?:@\[|/-|theorem\s|lemma\s|def\s|abbrev\s|structure\s|instance\s|class\s|"
                 r"namespace\s|end\b|section\b|open\s|variable\s|omit\s|include\s|set_option\s|"
                 r"noncomputable\s|scoped\s|attribute\s|#|local\s|example\s|import\s|universe\s|"
                 r"macro\s|syntax\s|elab\s|deriving\s|export\s|initialize\s)")
# the same, but a declaration may be indented: `PositiveAxisSystem.lean` indents
# nine of its declarations by one space, and a span that does not stop at them
# swallows the whole declaration.
IND = re.compile(r"^\s+(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                 r"(?:theorem|lemma|def|abbrev|structure|instance|class|inductive|example|"
                 r"section|namespace|end)\b")
PREFIX = re.compile(r"^(omit|include|variable|attribute|open)\b")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def comment_mask(lines):
    """mask[i] is True when line i is inside a `/- ... -/` block (or is a whole
    comment line).  Docstrings are prose: one of them contains the sentence
    "theorem makes no assertion of cancellation on every normalized band", and
    without this mask that sentence reads as a declaration."""
    mask = [False] * len(lines)
    inside = False
    for i, l in enumerate(lines):
        if not inside:
            if '/-' in l:
                mask[i] = True
                if '-/' not in l[l.index('/-') + 2:]:
                    inside = True
        else:
            mask[i] = True
            if '-/' in l:
                inside = False
    return mask


def is_prefix(l):
    s = l.strip()
    return (s.startswith('omit ') or s.startswith('include ') or s.startswith('attribute ')
            or (s.startswith('variable ') and s.endswith(' in'))
            or (s.startswith('open ') and s.endswith(' in')) or s.startswith('@['))


def span_for(lines, i):
    """i = index of the theorem line.  Returns (start, end), end exclusive.

    Asserts the invariant the deletion depends on: no *other* declaration begins
    inside the span.  Without this check a span that overruns an indented
    declaration (`PositiveAxisSystem.lean` indents nine of them) silently deletes
    a lemma that is still used elsewhere, and the build then fails with an
    unknown identifier far from the edit.  A span that contains a declaration is
    shortened to end just before it.
    """
    s = i
    while s > 0:
        prev = lines[s - 1]
        if prev.strip() == '' or prev.strip().startswith('--'):
            break
        if is_prefix(prev):
            s -= 1
            continue
        if prev.strip().endswith('-/'):                      # docstring block
            j = s - 1
            while j >= 0 and not lines[j].strip().startswith('/-'):
                j -= 1
            if j >= 0:
                s = j
                continue
        break
    e = i + 1
    while e < len(lines):
        l = lines[e]
        if not l.strip():
            e += 1
            continue
        if TOP.match(l) or DECL.match(l) or IND.match(l):
            break
        e += 1
    while e > i + 1 and not lines[e - 1].strip():
        e -= 1
    return s, e


def span_ok(lines, i, s, e, mask):
    """True when the span contains exactly one declaration, the one at i."""
    for k in range(s, e):
        if k != i and not mask[k] and (DECL.match(lines[k]) or IND.match(lines[k])):
            return False
    return True


def block_end(lines, i):
    """i = index of a column-0 `omit`/`include`/`variable`/`attribute` line.
    Returns the index one past the last line of that prefix block, or None if
    the line does not begin a prefix block at all -- `variable x` introducing a
    section variable is such a line, and so is `variable ... ` whose block is
    separated from it by a blank line."""
    j = i
    head = lines[i].strip()
    if head.startswith('attribute'):
        return None                       # `attribute [...]` is a command, not a prefix
    if head.startswith('open'):
        return i + 1 if head.endswith(' in') else None
    while j < len(lines):
        if not lines[j].strip():
            return None                                      # a section variable, not a prefix
        if lines[j].rstrip().endswith(' in'):
            return j + 1
        if j > i and not lines[j].startswith((' ', '\t')):
            return None                                      # not a continuation
        if j - i > 8:
            return None
        j += 1
    return None


def next_command(lines, j):
    """Index of the next command at or after j, skipping blanks, comments,
    docstrings, prefix blocks and attribute lines; len(lines) at end of file."""
    while j < len(lines):
        t = lines[j].strip()
        if not t or t.startswith('--'):
            j += 1
            continue
        if t.startswith('/-'):
            if t.endswith('-/'):
                j += 1
                continue
            j += 1
            while j < len(lines) and not lines[j].strip().endswith('-/'):
                j += 1
            j += 1
            continue
        if PREFIX.match(lines[j]):
            b = block_end(lines, j)
            if b is not None:
                j = b
                continue
            return j                                         # `variable` introducing a section variable
        if t.startswith('@['):
            rest, k = t, j
            while ']' not in rest and k + 1 < len(lines):
                k += 1
                rest += ' ' + lines[k].strip()
            if ']' in rest and rest.split(']', 1)[1].strip():
                return j                                     # attribute and command on one line
            j = k + 1
            continue
        return j
    return len(lines)


def _is_last(lines, j):
    """True when the next command after j is `end` or there is none."""
    j = next_command(lines, j)
    return j >= len(lines) or lines[j].strip().startswith('end')


def orphans(lines):
    """Index ranges of prefix blocks and docstrings with no command after them.

    A `attribute [...]` command needs no following declaration, and a `/-! ... -/`
    section heading is not a docstring; neither is reported."""
    out = []
    for i, l in enumerate(lines):
        if PREFIX.match(l) and not l.strip().startswith('attribute'):
            e = block_end(lines, i)
            if e is not None and _is_last(lines, e):
                out.append((i, e))
        t = l.strip()
        if t.startswith('/--'):
            k = i
            if not t.endswith('-/'):
                while k < len(lines) and not lines[k].strip().endswith('-/'):
                    k += 1
            if _is_last(lines, k + 1):
                out.append((i, k + 1))
    return out


def word_counts(roots):
    """Token counts over every `.lean` file reachable from `roots`; a file counts
    once.  `--also` paths are included so that a name used only from outside the
    directory being pruned (the root module, the comparator challenges, the
    scripts) protects its declaration."""
    words = collections.Counter()
    seen = set()
    for root in roots:
        paths = [root] if root.endswith('.lean') else lean_files(root)
        for p in paths:
            rp = os.path.realpath(p)
            if rp in seen:
                continue
            seen.add(rp)
            with open(p, errors='replace') as fh:
                words.update(TOKEN.findall(fh.read()))
    return words


def lean_files(root):
    return sorted(os.path.join(dp, f) for dp, _, fs in os.walk(root)
                  for f in fs if f.endswith('.lean'))


def main(argv):
    global KINDS
    dry = '--dry' in argv
    kinds = 'theorem|lemma'
    if '--kinds' in argv:
        k = argv.index('--kinds')
        kinds = argv[k + 1].replace(',', '|')
        del argv[k:k + 2]
        KINDS = kinds
        DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                          r"(" + KINDS + r")\s+([A-Za-z_][A-Za-z0-9_']*)")
    also = []
    argv = list(argv)
    while '--also' in argv:
        k = argv.index('--also')
        also += argv[k + 1].split(',')
        del argv[k:k + 2]
    protected = set()
    while '--keep' in argv:
        k = argv.index('--keep')
        protected |= {l.strip() for l in open(argv[k + 1]) if l.strip() and not l.startswith('#')}
        del argv[k:k + 2]
    excl = []
    while '--exclude' in argv:
        k = argv.index('--exclude')
        excl += argv[k + 1].split(',')
        del argv[k:k + 2]
    root = [a for a in argv if not a.startswith('--')][0]
    total_d = total_l = touched = 0
    for it in range(1, 200):
        words = word_counts([root] + also)
        for k in protected:                  # a protected name counts as used
            words[k] = max(words[k], 2)
        d_n = l_n = f_n = 0
        for p in lean_files(root):
            if any(p == e or p.endswith(os.sep + e) for e in excl):
                continue
            with open(p, errors='replace') as fh:
                lines = fh.read().split('\n')
            cut = set()
            mask = comment_mask(lines)
            for i, l in enumerate(lines):
                if mask[i]:
                    continue
                m = DECL.match(l)
                if not m or '@[' in l:
                    continue
                if words[m.group(2)] > 1:
                    continue
                s, e = span_for(lines, i)
                if not span_ok(lines, i, s, e, mask):
                    print(f"REFUSED {p}:{i + 1} {m.group(2)} (span holds another declaration)")
                    continue
                cut.update(range(s, e))
            if not cut:
                continue
            keep = [l for i, l in enumerate(lines) if i not in cut]
            # remove prefix blocks the deletion left without a command
            for _ in range(50):
                orp = orphans(keep)
                if not orp:
                    break
                drop = set()
                for s, e in orp:
                    drop.update(range(s, e))
                keep = [l for i, l in enumerate(keep) if i not in drop]
            removed = len(lines) - len(keep)
            if not dry:
                with open(p, 'w') as fh:
                    fh.write('\n'.join(keep))
            d_n += sum(1 for i, l in enumerate(lines)
                       if i in cut and DECL.match(l))
            l_n += removed
            f_n += 1
        print(f"pass {it}: {d_n} declarations, {l_n} lines, {f_n} files")
        total_d += d_n
        total_l += l_n
        touched += f_n
        if d_n == 0 or dry:
            break
    print(f"total: {total_d} declarations, {total_l} lines, {touched} files")


if __name__ == '__main__':
    main(sys.argv[1:])
