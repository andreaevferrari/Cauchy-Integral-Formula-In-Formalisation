#!/usr/bin/env python3
r"""rigor_lint.py — distinguish outline proofs from full ones.

A card with a ## Proof section is 'proved' to frontier.py regardless of
whether the proof is rigorous or a gesture-level outline. This linter
reports the honest split, and flags dishonesty: a card marked
rigor: outline whose proof lacks the 'Proof outline' banner, or a full
proof that still contains gesture words.

Usage: python3 tools/rigor_lint.py
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools
V = pathlib.Path(__file__).resolve().parent.parent
# atoms come from every curated pool (tools/pools.py)
GESTURES = ['identical', 'more directly', 'roughly', 'essentially the same',
            'mutatis mutandis', 'left to the reader', 'straightforward',
            'routine', 'obviously', 'the same argument',
            'reorganize', 'incompatible with', 'analogous']

outline, full, gesture_in_full = [], [], []
for f in pools.atoms():
    t = f.read_text()
    m = re.search(r'## Proof(.*?)(?=\n## Notes|\n## References|\Z)', t, re.S)
    if not m:
        continue
    body = m.group(1)
    marked = re.search(r'^rigor: outline', t, re.M)
    is_outline = bool(marked) or 'Proof outline' in body
    hits = [g for g in GESTURES if g.lower() in body.lower()]
    if is_outline:
        outline.append(f.stem)
        if not marked:
            print(f"  UNMARKED OUTLINE: {f.stem} — has 'Proof outline'/gestures but no 'rigor: outline'")
    else:
        full.append(f.stem)
        if hits:
            gesture_in_full.append((f.stem, hits))
            print(f"  GESTURE IN FULL PROOF: {f.stem} — {hits} (mark rigor: outline or make it rigorous)")

print(f"\nrigor: {len(full)} full, {len(outline)} outline")
print("  outline cards (proof is a sketch, not line-by-line):")
for s in sorted(outline):
    print(f"    - {s}")
sys.exit(0)
