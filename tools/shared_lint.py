#!/usr/bin/env python3
r"""shared_lint.py — the shared-item extractor (advisory).

As the graph grows, the same low-level mechanism gets re-written inline
in many proofs instead of being factored into one card that the rest
cite. This linter scans clean-pool proofs for recurring mechanism
phrases and reports those that appear in several cards but are not yet
their own card — extraction candidates.

Advisory: prints candidates and exits 0. Judgement (is it worth a card,
or a ground primitive?) stays human. Run alongside term_lint.

Usage: python3 tools/shared_lint.py [--threshold N]
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
# atoms come from every curated pool (tools/pools.py)

# mechanism -> (substrings that signal it, stem of the card that already factors it or None)
MECHANISMS = {
    'maximum principle':        (['maximum principle', 'comparison principle'], 'thm-maximum-principle'),
    'energy quantization':      (['concentrat', 'quantiz', 'quantum'], 'lem-energy-quantization'),
    'epsilon-regularity':       ['epsilon-regular', r'$\epsilon$-regular', 'small energy'],
    'removable singularity':    (['removable'], 'lem-removable-singularity-harmonic'),
    'Hardy space / BMO':        (['Hardy', 'BMO'], 'lem-hardy-holomorphic'),
    'Wente / compensated':      (['Wente', 'compensated'], 'lem-wente'),
    'conformal rescaling':      (['conformal dilation', 'conformal rescal', 'rescal', 'dilation'], None),
    'weak W12 compactness':     (['weak $W', 'weakly', 'weak compact'], None),
    'nearest-point projection': (['nearest-point', 'nearest point', 'projection to $M', 'projection back'], None),
    'Pohozaev / conservation':  (['Pohozaev', 'conservation law'], None),
    'Coulomb / moving frame':   (['Coulomb', 'moving frame', 'moving-frame'], None),
    'del-bar / Fredholm index': (['bar\\partial', 'Dolbeault', 'Fredholm', 'index of the'], None),
    'Bochner identity':         (['Bochner', 'Rellich', 'Wirtinger'], None),
    'mountain pass':            (['mountain-pass', 'mountain pass', 'min-max critical'], None),
}

def proof_of(t):
    m = re.search(r'## Proof\n(.*?)(?=\n## Notes|\n## References|\Z)', t, re.S)
    return m.group(1) if m else ''

thr = 3
if '--threshold' in sys.argv:
    thr = int(sys.argv[sys.argv.index('--threshold') + 1])

stem2path = {f.stem: f for f in pools.atoms()}
hits = {}
for f in pools.atoms():
    body = proof_of(f.read_text())
    if not body:
        continue
    for name, spec in MECHANISMS.items():
        subs = spec[0] if isinstance(spec, tuple) else spec
        if any(s in body for s in subs):
            hits.setdefault(name, []).append(f.stem)

print("shared-item extraction scan (proofs only):\n")
candidates = 0
for name, spec in MECHANISMS.items():
    card = spec[1] if isinstance(spec, tuple) else None
    cards = hits.get(name, [])
    n = len(cards)
    if card:
        # already factored — flag any proof that re-states it without linking the card
        unlinked = [c for c in cards if f'[[{card}' not in stem2path[c].read_text()] if cards else []
        if unlinked:
            print(f"  [{name}] factored as [[{card}]] but re-stated without linking in: {', '.join(unlinked)}")
            candidates += 1
    elif n >= thr:
        print(f"  [{name}] appears in {n} proofs, NOT yet a card → extract candidate: {', '.join(sorted(cards))}")
        candidates += 1
print(f"\nshared lint: {candidates} extraction candidate(s) — advisory, judge by hand")
sys.exit(0)
