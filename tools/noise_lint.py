#!/usr/bin/env python3
r"""noise_lint.py — the clean pool carries mathematics only.

Statement and Proof sections of curated-pool atoms must contain no
bibliographic noise: no source/author names, no cf./see, no chapter or
section pointers, no bibliography links. Premise citations as [[wikilinks]]
are the one permitted form of reference; everything else belongs in Notes.

Exit 1 on any hit. Run alongside render_lint before committing.
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
# The author list is the vault's own (tools/pools.py): the names a vault is
# tempted to write into a statement are the ones its sources are by.
BAD = re.compile(
    r'\[\[ref-|\bcf\.|\bsee\s+(?:\[\[|§|[Cc]hapter|[Ss]ection|below|above)'
    r'|\bchapter\b|\bch-\d|§|\bpool\b|\bibid\b'
    + ''.join('|' + a for a in pools.AUTHORS), re.I)

bad = 0
for f in pools.atoms():
    t = f.read_text()
    # A card whose text is a source's, unaltered, is not ours to police. The
    # paper cites works inside its statements and names its own results after
    # people; reproducing that is the point. `verbatim:` marks those, and a
    # card without it is one somebody wrote here and the rules apply.
    if re.search(r'^verbatim:', t, re.M):
        continue
    m = re.search(r'## Statement\n(.*?)(?=\n## Notes|\n## References|\Z)', t, re.S)
    if not m:
        continue
    for i, ln in enumerate(m.group(1).split('\n')):
        if BAD.search(ln):
            print(f'{f}: {ln.strip()[:100]}')
            bad += 1
print('noise lint: clean' if not bad else f'{bad} offending line(s)')
sys.exit(1 if bad else 0)
