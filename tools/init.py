#!/usr/bin/env python3
r"""init.py — turn the template into a vault about something.

One mechanical step, done wrong easily and by hand every time otherwise:
the pool directory carries the subject's name, and `tools/pools.py` has to
agree with it. Everything else about instantiating — what the README says,
which sources go in the bibliography, what the root card is — is writing,
and writing is not this script's business.

    python3 tools/init.py Kakeya            # → KakeyaHypergraph/
    python3 tools/init.py Kakeya --root thm-kakeya-set-conjecture

Run once from the vault root, then delete this file: a vault that already
knows what it is about has no use for it.
"""
import pathlib, re, shutil, sys

V = pathlib.Path(__file__).resolve().parent.parent
TEMPLATE_POOL = 'NetworkHypergraph'


def main(argv):
    if not argv or argv[0].startswith('-'):
        sys.exit(__doc__.strip())
    name = argv[0]
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*', name):
        sys.exit(f'{name!r}: the pool name becomes a directory and a wikilink '
                 'prefix — letters and digits only, starting with a letter')
    root = ''
    if '--root' in argv:
        root = argv[argv.index('--root') + 1]

    src, dst = V / TEMPLATE_POOL, V / f'{name}Hypergraph'
    if not src.exists():
        sys.exit(f'{TEMPLATE_POOL}/ is gone — this vault has already been '
                 'initialized, and tools/init.py should have been deleted')
    if dst.exists():
        sys.exit(f'{dst.name}/ already exists')
    shutil.move(str(src), str(dst))

    p = V / 'tools' / 'pools.py'
    t = p.read_text()
    t = t.replace(f"CLEAN = [V / '{TEMPLATE_POOL}']", f"CLEAN = [V / '{dst.name}']")
    if root:
        t = re.sub(r"^ROOT = ''$", f"ROOT = '{root}'", t, count=1, flags=re.M)
    p.write_text(t)

    print(f'pool     {TEMPLATE_POOL}/ → {dst.name}/')
    print(f'pools.py CLEAN → [{dst.name}]' + (f", ROOT → {root}" if root else ''))
    print('\nNext, by hand:')
    print(f'  - {dst.name}/notation.md   the cast and the symbol table')
    print('  - README.md, CLAUDE.md      what this vault is about')
    print('  - tools/pools.py AUTHORS    the surnames your sources are by')
    print('  - rm tools/init.py')


if __name__ == '__main__':
    main(sys.argv[1:])
