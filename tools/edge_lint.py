#!/usr/bin/env python3
r"""edge_lint.py — the edges must mirror the text, exactly.

For every atom in every curated pool:
  * each [[link]] in its Statement demands a references- or depends-edge
    to that target;
  * each [[link]] in its Proof demands a uses-edge;
and conversely every edge file must be witnessed by such a link
(no phantom edges). Exit 1 on any mismatch.
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
# every curated pool: an edge lives with its SOURCE, its target may not
LINK = re.compile(r'\[\[([^\]|#]+)')

# collect edges: (src, tgt) -> kind
edges = {}
for f in pools.edges():
    t = f.read_text()
    kind = (re.search(r'^kind: (\S+)', t, re.M) or [None, '?'])[1]
    refs = re.findall(r'"\[\[([^\]]+)\]\]"', t)
    if len(refs) == 2:
        edges[(refs[0], refs[1])] = kind

# a definition target is a term reference wherever it is cited
def_stems = {f.stem for f in pools.atoms() if f.parent.name == 'definitions'}

wanted = {}   # (src, tgt) -> 'statement' | 'proof' | 'term'
for f in pools.atoms():
    t = f.read_text()
    stmt = re.search(r'## Statement\n(.*?)(?=\n## Proof|\n## Notes|\n## References|\Z)', t, re.S)
    proof = re.search(r'## Proof\n(.*?)(?=\n## Notes|\n## References|\Z)', t, re.S)
    for tgt in LINK.findall(stmt.group(1) if stmt else ''):
        tgt = tgt.strip()
        if tgt != f.stem:
            wanted[(f.stem, tgt)] = 'term' if tgt in def_stems else 'statement'
    for tgt in LINK.findall(proof.group(1) if proof else ''):
        tgt = tgt.strip()
        if tgt != f.stem:
            wanted.setdefault((f.stem, tgt), 'term' if tgt in def_stems else 'proof')

bad = 0
for (s, t), where in sorted(wanted.items()):
    kind = edges.get((s, t))
    if kind is None:
        print(f'missing edge: {s} → {t}  (cited in {where})')
        bad += 1
    elif where == 'term' and kind != 'references':
        print(f'kind mismatch: {s} → {t} is {kind}, but the target is a definition (references)')
        bad += 1
    elif where == 'proof' and kind != 'uses':
        print(f'kind mismatch: {s} → {t} is {kind}, but cited in a proof (uses)')
        bad += 1
    elif where == 'statement' and kind != 'depends':
        print(f'kind mismatch: {s} → {t} is {kind}, but a statement builds on a non-definition (depends)')
        bad += 1
for (s, t), kind in sorted(edges.items()):
    if (s, t) not in wanted:
        print(f'phantom edge: {s} → {t} ({kind}) — no witnessing link in the text')
        bad += 1
print('edge lint: clean' if not bad else f'{bad} mismatch(es)')
sys.exit(1 if bad else 0)
