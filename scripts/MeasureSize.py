"""Measure the size of a library: files, physical lines, theorem/lemma count.

Usage:  python3 MeasureSize.py <dir> [<dir> ...]
        git archive HEAD NavierStokes | tar -xO | python3 MeasureSize.py --stdin

A theorem/lemma is counted at any indentation level, with or without an
`@[...]`, `private`, `protected`, `noncomputable` or `scoped` prefix; this is
the definition used in the paper's Table 1.
"""
import os, re, sys

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                  r"(theorem|lemma)\s+[A-Za-z_]")


def count_text(paths):
    files = lines = decls = 0
    for p in paths:
        files += 1
        with open(p, errors='replace') as fh:
            for l in fh:
                lines += 1
                if DECL.match(l):
                    decls += 1
    return files, lines, decls


def walk(d):
    out = []
    for dp, _, fs in os.walk(d):
        out += [os.path.join(dp, f) for f in fs if f.endswith('.lean')]
    return sorted(out)


if __name__ == '__main__':
    args = sys.argv[1:]
    if args == ['--stdin']:
        lines = sys.stdin.read().split('\n')
        d = sum(1 for l in lines if DECL.match(l))
        print(f"stdin (a concatenation, not a file count): lines {len(lines)-1} "
              f"theorem/lemma {d}")
    else:
        for a in args:
            f, l, d = count_text(walk(a))
            print(f"{a:24} files {f:6}  lines {l:8}  theorem/lemma {d:7}")
