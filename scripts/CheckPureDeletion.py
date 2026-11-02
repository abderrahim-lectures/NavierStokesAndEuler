"""Check that a prune only deleted whole blocks and changed nothing else.

For each file under `dir` it diffs the working tree against `HEAD` and requires:

  1. the working-tree file is the committed file with a set of *contiguous line
     ranges deleted* -- no line inserted, none edited, none reordered.  This is
     checked by a two-pointer walk that may only skip committed lines;
  2. every deleted range starts on a declaration boundary: its first non-blank
     line begins with a declaration keyword, an `@[...]` attribute, a docstring,
     or a prefix keyword (`omit`/`include`/`variable`/`open`), or the range is
     whitespace only;
  3. every deleted range is balanced in `(`/`)`, `[`/`]`, `{`/`}` and `⟨`/`⟩`
     after blanking comments and strings -- an unbalanced range means a span was
     cut through the middle of a term.

Used on a library whose build cannot be used as the gate (`Euler` does not
elaborate, at 29 sites that predate this work), this is the strongest available
structural check.

    python3 CheckPureDeletion.py Euler [Euler.lean ...]
"""
import os
import subprocess
import sys
import collections

BOUNDARY = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class',
            'inductive', 'example', 'section', 'namespace', 'end', 'open', 'variable',
            'omit', 'include', 'attribute', 'set_option', 'noncomputable', 'scoped',
            'local', '@[', '/--', '/-!', 'import', 'universe', 'private', 'protected',
            'mutual', 'deriving', '#')
PAIRS = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}


BASE = os.environ.get('PRUNE_BASE', 'HEAD')


def committed(path):
    r = subprocess.run(['git', 'show', f'{BASE}:{path}'], capture_output=True, text=True)
    return r.stdout.split('\n') if r.returncode == 0 else None


def strip_comments_and_strings(text):
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith('/-', i):
            j = text.find('-/', i + 2)
            i = n if j < 0 else j + 2
            out.append(' ')
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            i = j + 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def balanced(lines):
    depth = collections.Counter()
    for l in strip_comments_and_strings('\n'.join(lines)).split('\n'):
        for ch in l:
            if ch in PAIRS:
                depth[ch] += 1
            elif ch in PAIRS.values():
                for k, v in PAIRS.items():
                    if v == ch:
                        depth[k] -= 1
                        if depth[k] < 0:
                            return False
    return all(v == 0 for v in depth.values())


def deletions(old, new):
    """Two-pointer walk: returns the deleted ranges, or None if `new` is not
    `old` with whole lines removed."""
    out, i, j = [], 0, 0
    while i < len(old) and j < len(new):
        if old[i] == new[j]:
            i += 1
            j += 1
            continue
        k = i
        while k < len(old) and old[k] != new[j]:
            k += 1
        if k == len(old):
            return None
        out.append((i, k))
        i = k
    if j < len(new):
        return None
    if i < len(old):
        out.append((i, len(old)))
    # a blank line can align with any other blank line, splitting one deletion in
    # two; merge ranges separated only by blanks
    merged = []
    for s, e in out:
        if merged and all(not l.strip() for l in old[merged[-1][1]:s]):
            merged[-1] = (merged[-1][0], e)
        else:
            merged.append((s, e))
    return merged


def main(paths):
    bad = 0
    total_blocks = total_lines = 0
    for root in paths:
        files = [root] if root.endswith('.lean') else sorted(
            os.path.join(dp, f) for dp, _, fs in os.walk(root) for f in fs
            if f.endswith('.lean'))
        for p in files:
            old = committed(p)
            if old is None:
                continue
            with open(p, errors='replace') as fh:
                new = fh.read().split('\n')
            if old == new:
                continue
            d = deletions(old, new)
            if d is None:
                print(f"CHANGED {p}: not a pure deletion")
                bad += 1
                continue
            total_lines += len(old) - len(new)
            for s, e in d:
                total_blocks += 1
                first = next((l.strip() for l in old[s:e] if l.strip()), '')
                if first and not first.startswith(BOUNDARY):
                    print(f"BOUNDARY {p}:{s + 1}: block starts with {first[:70]!r}")
                    bad += 1
                if not balanced(old[s:e]):
                    print(f"UNBALANCED {p}:{s + 1}-{e}: {first[:60]!r}")
                    bad += 1
    print(f"{total_blocks} deleted blocks, {total_lines} lines, {bad} problems")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
