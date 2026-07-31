#!/usr/bin/env python3
r"""bundle_lint.py — a definition card carrying more than one notion (advisory).

A card that declares several things costs the graph resolution it exists to
keep. If half the consumers of a card use only part of what it declares, then
every edge into it says less than it could: "uses this card" when the fact is
"uses one of the three things on it".

The test is not "one symbol per card". Slabs and planks live together because
every consumer uses both; separated and maximal live together for the same
reason. What earns a split is a consumer that uses a proper subset — and the
split is then a card plus a references edge, exactly as Hausdorff dimension
already sits beside Hausdorff measure rather than inside it.

One limitation, and it produces the obvious false positive. Notions are matched
by the WORDS in the title, so a notion prose only ever writes as a symbol looks
unused. `def-shading` declares the shading and the region it covers; the second
is written $U(\mathbb{V},Y)$ and essentially never spelled out, so it reads as
21 of 22 consumers using a proper subset when in fact none of them can use $U$
without the shading it is built from. Check a hit before acting on it: the
question is whether a consumer uses one notion *without* the other, not whether
it happens to spell both out.

Advisory: prints and exits 0.

Usage: python3 tools/bundle_lint.py [--threshold 0.34]
"""
import re, sys, collections
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

THRESHOLD = 0.34
if '--threshold' in sys.argv:
    THRESHOLD = float(sys.argv[sys.argv.index('--threshold') + 1])

cards = {f.stem: (f.read_text(), f.parent.name) for f in pools.atoms()}


def statement(text):
    m = re.search(r'## Statement\n(.*?)(?=\n## Proof|\n## Notes|\Z)', text, re.S)
    return m.group(1).lower() if m else ''


flagged = 0
for stem, (text, kind) in sorted(cards.items()):
    if kind != 'definitions':
        continue
    h = re.search(r'^#\s+.*?—\s*(.+)$', text, re.M)
    if not h:
        continue
    # the notions this card declares, one per comma- or and-separated part
    parts = [p for p in pools.phrases_of(h.group(1))]
    heads = sorted({p for p in parts if not p.endswith('s')} or parts)
    if len(heads) < 2:
        continue

    users = [s for s, (t, _) in cards.items() if s != stem and f'[[{stem}' in t]
    if len(users) < 3:
        continue

    tally = collections.Counter()
    for u in users:
        s = statement(cards[u][0])
        used = tuple(sorted(h for h in heads if re.search(r'(?<![a-z])' + re.escape(h) + r's?(?![a-z])', s)))
        tally[used] += 1
    partial = sum(n for combo, n in tally.items() if combo and len(combo) < len(heads))
    if partial / len(users) < THRESHOLD:
        continue

    flagged += 1
    print(f'{stem}  declares {len(heads)}: {", ".join(heads)}')
    print(f'   {len(users)} consumers, {partial} use a proper subset')
    for combo, n in tally.most_common():
        print(f'     {n:>2} x  {", ".join(combo) if combo else "(none of them by name)"}')

print(f'\nbundle lint: {flagged} over-full card(s) — advisory, judge by hand')
sys.exit(0)
