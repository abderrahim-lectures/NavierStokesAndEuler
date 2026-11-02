"""Replace the proof of every declaration that fails to elaborate by `sorry`.

This is a *verification harness*, not a change to keep: the patched tree is built
only to obtain object files for modules that cannot be built otherwise, so that a
refactoring elsewhere in the library can be type-checked against them. The
patched files are restored afterwards, byte for byte.

    python3 scripts/SorryPatch.py Euler/EulerProof.lean:2432 Euler/GevreyComposition.lean:51
    python3 scripts/SorryPatch.py --revert

The enclosing declaration is found by scanning up for a line at column 0 that
starts a declaration, and its end by scanning down for the next such line. The
declaration keeps its statement, including everything up to `:=`, and gets
`:= by sorry` as its proof.
"""
import re
import subprocess
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|example|structure|class)\b")
TOP = re.compile(r"^(?:@\[|/-|theorem\s|lemma\s|def\s|abbrev\s|structure\s|instance\s|class\s|"
                 r"namespace\s|end\b|section\b|open\s|variable\s|omit\s|include\s|set_option\s|"
                 r"noncomputable\s|scoped\s|attribute\s|#|local\s|example\s|import\s|universe\s|"
                 r"macro\s|syntax\s|elab\s|deriving\s|export\s|initialize\s)")


def decl_start(lines, i):
    j = i
    while j >= 0 and not DECL.match(lines[j]):
        j -= 1
    return j


def decl_end(lines, i):
    j = i + 1
    while j < len(lines) and not (TOP.match(lines[j])):
        j += 1
    while j > i + 1 and not lines[j - 1].strip():
        j -= 1
    return j


def patch(path, line):
    lines = open(path, errors='replace').read().split('\n')
    s = decl_start(lines, line - 1)
    e = decl_end(lines, s)
    if s < 0:
        print(f'  {path}:{line}: no enclosing declaration')
        return False
    # the statement runs to the first `:=` at the declaration's own indent level
    k = s
    while k < e and ':=' not in lines[k]:
        k += 1
    if k >= e:
        print(f'  {path}:{line}: no `:=` in the declaration')
        return False
    head = lines[k].split(':=')[0]
    new = lines[:s] + lines[s:k] + [head + ':= by sorry', ''] + lines[e:]
    open(path, 'w').write('\n'.join(new))
    print(f'  {path}:{line}: declaration at line {s + 1} replaced by sorry')
    return True


def main(argv):
    if '--revert' in argv:
        r = subprocess.run(['git', 'checkout', '--', 'Euler'], capture_output=True, text=True)
        print('reverted Euler/ to the committed state', r.returncode)
        return
    # group by file and patch bottom-up: two error sites in one declaration must
    # be patched once, and a patch changes the line numbers below it
    byfile = {}
    for a in argv:
        path, line = a.rsplit(':', 1)
        byfile.setdefault(path, []).append(int(line))
    for path, lines in byfile.items():
        src = open(path, errors='replace').read().split('\n')
        starts = sorted({decl_start(src, l - 1) for l in lines}, reverse=True)
        print(f'{path}: {len(lines)} sites in {len(starts)} declarations')
        for st in starts:
            patch(path, st + 1)


if __name__ == '__main__':
    main(sys.argv[1:])
