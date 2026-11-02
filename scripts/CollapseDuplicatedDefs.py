"""Point a duplicated definition at the definition it duplicates.

Two project `def`s with the same type and the same value are the same constant
under two names. Leaving both bodies in place invites drift: fix a formula in one
and the other silently disagrees. This rewrites the body of every duplicate to the
name of the one it duplicates, keeping its own name (so no use site changes).

    python3 .scratch/dedupe_defs.py --dry
    python3 .scratch/dedupe_defs.py

Input is `.scratch/dupval.txt`, one group per line: canonical, others, type.
"""
import re
import sys

TOP = re.compile(r"^(?:@\[|/-|theorem\s|lemma\s|def\s|abbrev\s|structure\s|instance\s|class\s|"
                 r"namespace\s|end\b|section\b|open\s|variable\s|set_option\s|noncomputable\s|"
                 r"scoped\s|attribute\s|#|local\s|example\s|import\s|universe\s)")
GENERATED = ('.casesOn', '.recOn', '.rec', '.mk', '.noConfusion', '.injEq', '.inj',
             '._flat_ctor', '.sizeOf_spec', '.elim', '.below', '.brecOn', '.ibelow',
             '.binductionOn', '.inductionOn', '.toCtorIdx', '.ctorIdx')


def declaration_in(path, short):
    """(start, end) of the declaration of `short` at column 0 of `path`."""
    lines = open(path, errors='replace').read().split('\n')
    pat = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*'
                     r'(?:def|abbrev)\s+' + re.escape(short) + r'\b')
    for i, l in enumerate(lines):
        if pat.match(l):
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]):
                j += 1
            return i, j
    return None


NAME_TO_MODULE = {}
for _l in open('.scratch/t5.tsv'):
    _x = _l.rstrip('\n').split('\t')
    if len(_x) == 3:
        NAME_TO_MODULE[_x[0]] = _x[1]


def module_of(full):
    """`NavierStokes.Foo.bar` -> `NavierStokes/Foo.lean`, from the declaration dump
    (the namespace is not always the module path, which is the point of the merges)."""
    mod = NAME_TO_MODULE.get(full)
    if mod is None:
        return None
    return mod.replace('.', '/') + '.lean'


def main(argv):
    dry = '--dry' in argv
    applied = skipped = 0
    for line in open('.scratch/dedup_ok.txt'):
        dup, canon = line.rstrip('\n').split('\t')
        if any(s in canon or s in dup for s in GENERATED):
            continue
        if True:
            path = module_of(dup)
            if path is None or not __import__('os').path.exists(path):
                print(f'  skip {dup}: no module')
                skipped += 1
                continue
            sp = declaration_in(path, dup.split('.')[-1])
            if not sp:
                print(f'  skip {dup}: declaration not found in {path}')
                skipped += 1
                continue
            i, j = sp
            lines = open(path, errors='replace').read().split('\n')
            k = i
            while k < j and ':=' not in lines[k]:
                k += 1
            if k >= j:
                print(f'  skip {dup}: no :=')
                skipped += 1
                continue
            head = lines[k].split(':=')[0]
            new = lines[:k] + [head + ':= ' + canon] + lines[j:]
            if not dry:
                open(path, 'w').write('\n'.join(new))
            print(f'  {dup}  :=  {canon}')
            applied += 1
    print(f'{"would apply" if dry else "applied"} {applied}, skipped {skipped}')


if __name__ == '__main__':
    main(sys.argv[1:])
