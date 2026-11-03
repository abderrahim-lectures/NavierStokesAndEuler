"""Find imports a module does not need.

A file's imports are tested one at a time by elaborating *that file only*
(`lake env lean`), which takes a couple of seconds and does not rebuild the library.
The result is a candidate list; it is not applied on its own, because removing an
import from F also removes it from everything that imports F and was relying on
getting it transitively. So this script only reports:

    python3 scripts/UnusedImports.py NavierStokes/Foo.lean ... > candidates.txt

Apply them in batches and gate on a full `lake build NavierStokes`, reverting the
files the build names.
"""
import os
import subprocess
import sys


def check(path):
    """Imports of `path` that can be removed without changing what it elaborates."""
    src = open(path, errors='replace').read()
    imports = [l for l in src.split('\n') if l.startswith('import ')]
    out = []
    for imp in imports:
        trial = src.replace(imp + '\n', '', 1)
        open(path, 'w').write(trial)
        r = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
        if r.returncode == 0:
            out.append(imp)
        open(path, 'w').write(src)
    return imports, out


def main(paths):
    total = redundant = 0
    for p in paths:
        if not os.path.exists(p):
            continue
        imports, unused = check(p)
        total += len(imports)
        redundant += len(unused)
        for u in unused:
            print(f'{p}\t{u[len("import "):]}')
    print(f'# {redundant} redundant of {total} tested', file=sys.stderr)


if __name__ == '__main__':
    main(sys.argv[1:])
