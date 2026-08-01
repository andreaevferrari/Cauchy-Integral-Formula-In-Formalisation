#!/usr/bin/env python3
r"""cone.py — proof-cone health check for any card.

Given a top card, walk its proof-dependency cone (uses/depends/references
edges) and report:
  * leaves      — cards depending on no further statement (the basic
                  landing points: everything bottoms out here);
  * debts       — statements in the cone without a Proof section (the
                  breakpoints: where the network is not yet expanded),
                  grouped by the source they are attributed to;
  * a one-line verdict: is the cone logically closed (every path ends at
                  a proved leaf or a definition/ground), or are there
                  open breakpoints?

Usage: python3 tools/cone.py <top-card-stem> [<top-card-stem> ...]
       python3 tools/cone.py            # the vault's root, tools/pools.py
"""
import re, sys, pathlib, collections
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
# atoms and edges come from every curated pool (tools/pools.py)

edges = {}
for ef in pools.edges():
    refs = re.findall(r'"\[\[([^\]]+)\]\]"', ef.read_text())
    if len(refs) == 2:
        edges.setdefault(refs[0], []).append(refs[1])

meta = {}
for f in pools.atoms():
    t = f.read_text()
    typ = (re.search(r'^type: (\w+)', t, re.M) or [None, '?'])[1]
    # Debts group by where the mathematics comes from: the first bibliography
    # card the atom cites. Which body of work a breakpoint belongs to is the
    # question you ask when deciding what to read next.
    m = re.search(r'\[\[ref-([^\]|#]+)', t)
    meta[f.stem] = (typ, '## Proof' in t, m.group(1) if m else '(unattributed)')

clean = set(meta)
tops = sys.argv[1:] or ([pools.ROOT] if pools.ROOT else [])
if not tops:
    sys.exit('no card given and tools/pools.py declares no ROOT')

for top in tops:
    if top not in clean:
        print(f"{top}: not a clean-pool card"); continue
    seen = set(); stack = [top]
    while stack:
        n = stack.pop()
        if n in seen: continue
        seen.add(n)
        stack += [e for e in edges.get(n, []) if e in clean]
    stmt = {n for n in seen if meta[n][0] not in ('definition', 'remark')}
    leaves, debts = [], []
    for n in stmt:
        outs = [e for e in edges.get(n, []) if e in clean and meta[e][0] not in ('definition', 'remark')]
        if not outs:
            leaves.append(n)
        if not meta[n][1]:
            debts.append(n)
    proved_leaves = [l for l in leaves if meta[l][1]]
    closed = len(debts) == 0
    print(f"\n=== cone of [[{top}]] ===")
    print(f"  statements in cone : {len(stmt)}")
    print(f"  leaves (landing)   : {len(leaves)}  ({len(proved_leaves)} proved, {len(leaves)-len(proved_leaves)} debt)")
    print(f"  debts (breakpoints): {len(debts)}", end='')
    if debts:
        by_src = collections.Counter(meta[d][2] for d in debts)
        print('  — ' + ', '.join(f'{n} {s}' for s, n in by_src.most_common()))
        w = max(len(meta[d][2]) for d in debts)
        for d in sorted(debts, key=lambda d: (meta[d][2], d)):
            print(f"      [{meta[d][2]:{w}}] {d}")
    else:
        print()
    print(f"  VERDICT: {'CLOSED — every path ends at a proved leaf or a definition' if closed else 'OPEN — '+str(len(debts))+' breakpoints remain'}")
