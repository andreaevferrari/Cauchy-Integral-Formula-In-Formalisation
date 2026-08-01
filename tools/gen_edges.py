#!/usr/bin/env python3
r"""gen_edges.py — write the edge files the text already demands.

rules.md § 2 makes edges a mirror of the links: a Statement link to a
definition is `references`, to a result `depends`; a Proof link to a result
is `uses`. That mapping is total, so the files can be written rather than
typed — `edge_lint.py` stays the check, this is only the hand.

Wipes and rebuilds `edges/`, so an edge whose link was deleted disappears
instead of lingering as a phantom. Run it, then `assign_ids.py`, then
`edge_lint.py`.
"""
import re, sys, shutil, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).parent)); import pools

LINK = re.compile(r'\[\[([^\]|#]+)')
pool = pools.CLEAN[0]
if (pool / 'edges').exists():
    shutil.rmtree(pool / 'edges')

def_stems = {f.stem for f in pools.atoms() if f.parent.name == 'definitions'}
wanted = {}
for f in pools.atoms():
    t = f.read_text()
    stmt = re.search(r'## Statement\n(.*?)(?=\n## Proof|\n## Notes|\n## References|\Z)', t, re.S)
    proof = re.search(r'## Proof\n(.*?)(?=\n## Notes|\n## References|\Z)', t, re.S)
    for tgt in LINK.findall(stmt.group(1) if stmt else ''):
        tgt = tgt.strip()
        if tgt != f.stem:
            wanted[(f.stem, tgt)] = 'references' if tgt in def_stems else 'depends'
    for tgt in LINK.findall(proof.group(1) if proof else ''):
        tgt = tgt.strip()
        if tgt != f.stem:
            wanted.setdefault((f.stem, tgt), 'references' if tgt in def_stems else 'uses')

for (s, t), kind in sorted(wanted.items()):
    d = pool / 'edges' / kind
    d.mkdir(parents=True, exist_ok=True)
    (d / f'{s}→{t}.md').write_text(
        f'---\nkind: {kind}\nref:\n  - "[[{s}]]"\n  - "[[{t}]]"\n---\n\n'
        f'# `{s}` → `{t}`\n\n**{kind}**: [[{s}]] {kind} [[{t}]] — link.\n')

import collections
c = collections.Counter(wanted.values())
print(f"edges written: {len(wanted)}  " + "  ".join(f"{k} {v}" for k, v in sorted(c.items())))
