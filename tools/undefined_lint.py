#!/usr/bin/env python3
r"""undefined_lint.py — a term used and never declared (advisory).

Scans every curated-pool Statement for terms this pool has a definition card
for, and reports the ones whose card is not linked *anywhere* in that atom.
That is the strict failure: not a bare later repeat, which rules.md allows,
but a concept invoked with nothing in the graph connecting it to its meaning.

The vocabulary is derived from the pool's own definition-card titles by
`pools.definition_terms()`. It used to be a hardcoded list, and the list was
another vault's — so this reported a clean pool by checking for terms that did
not exist here. A linter whose subject is not the thing in front of it reports
nothing and means nothing.

With `--fix` it inserts the missing links, under four restrictions that exist
because a link here is not a formatting choice:

  * only where the card is linked NOWHERE in that atom — a later bare repeat
    is allowed by rules.md § 5 and linking every occurrence is unreadable;
  * only at the first occurrence, for the same reason;
  * only for terms of two words or more. Single words are where the matching
    goes wrong: "dimension" fires inside "three dimensions" and "Hausdorff
    dimension", and a wrong link is worse than a missing one because it also
    manufactures an edge;
  * never silently — the diff is printed, and `--fix` must be asked for.

**Inserting a link changes the card's id.** `assign_ids` hashes the Statement
with `[[a|b]]` folded to `[[a]]`, so a bare term becoming a link changes the
hashed text. Run this before anything is published, or accept that saved links
to the re-addressed cards will break.

Advisory: exits 0. Usage: python3 tools/undefined_lint.py [--fix]
"""
import re, sys
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

FIX = '--fix' in sys.argv

terms = pools.definition_terms()
phrases = sorted(terms, key=len, reverse=True)

hits = fixed = 0
for f in pools.atoms():
    t = f.read_text()
    m = re.search(r'## Statement\n(.*?)(?=\n## Proof|\n## Notes|\Z)', t, re.S)
    if not m:
        continue
    body = m.group(1)
    low = re.sub(r'\$\\(alpha|beta|gamma|delta|epsilon|eta|theta|kappa|lambda|mu|nu|rho'
                 r'|sigma|tau|phi|chi|psi|omega)\$', lambda g: g.group(1), body).lower()
    seen = []
    for ph in phrases:
        card = terms[ph]
        if card == f.stem or f'[[{card}' in t:
            continue                                   # declared somewhere in this atom
        for mm in re.finditer(r'(?<![a-z])' + re.escape(ph) + r'(?![a-z])', low):
            s, e = mm.start(), mm.end()
            if any(a <= s < e <= b for a, b in seen):   # inside a longer phrase already reported
                continue
            seen.append((s, e))
            hits += 1
            if FIX and ' ' in ph:
                # rewrite the first occurrence, preserving the text as written
                shown = body[s:e]
                fixed_body = body[:s] + f'[[{card}|{shown}]]' + body[e:]
                t = t[:m.start(1)] + fixed_body + t[m.end(1):]
                f.write_text(t)
                print(f'{f.stem}: "{shown}" -> [[{card}|{shown}]]')
                fixed += 1
            else:
                why = '' if ' ' in ph else '   (single word — not auto-linked)'
                print(f'{f.stem} [Statement]: "{ph}" used, [[{card}]] never linked here{why}')
            break
if FIX:
    print(f'\nundefined lint: {fixed} link(s) inserted of {hits} candidate(s).')
    print('ids have changed — run assign_ids.py, then edges and edge_lint.')
else:
    print(f'\nundefined lint: {hits} undeclared use(s) — advisory, judge by hand')
    print('re-run with --fix to insert the multi-word ones (this changes ids).')
sys.exit(0)
