#!/usr/bin/env python3
r"""hedge_lint.py — a hedge in a Statement names a symbol or it is not mathematics.

The pool has three asymptotic relations and they are stated precisely in
`notation.md`. What was never stated is which English word means which one, so
"roughly the same" could be read as $\eqsim$, as $\lessapprox$, or as nothing
at all — and twice it was nothing at all: a definition of constant
multiplicity that never said in what sense the multiplicity was constant, and
a lemma hypothesis that never said in what sense two quantities agreed.

A hedge is allowed here in exactly four positions:

  * in the card's own title — a card may use the word it is named after,
    which is what makes *essentially distinct* and *typical angle* names
    rather than hedges;
  * inside a wikilink's display half — it is part of a term with a card;
  * inside *italics* — it is the definiendum of the card being read;
  * beside a relation symbol — it is glossing that symbol in words.

Callout headers are titles, not prose, and are skipped.

Anything else is flagged. Notes are not checked: commentary is where a word
like *morally* belongs, and the point of the rule is that it stays there.

Fatal, like the other Statement-level checks. Usage: python3 tools/hedge_lint.py
"""
import re, sys
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

HEDGES = [
    'roughly', 'approximately', 'comparable', 'essentially', 'typical',
    'morally', 'more or less', 'in some sense', 'basically', 'heuristically',
    'nearly', 'about the same', 'similar',
]
RELATION = re.compile(r'\\(eqsim|lesssim|gtrsim|lessapprox|gtrapprox|approx|sim|le|ge|leq|geq)\b')
NEAR = 45   # characters either side within which a symbol counts as the gloss


def licensed(body, m, title):
    """Is this occurrence in one of the four allowed positions?"""
    # the card's own name
    if m.group(0).lower() in title:
        return True
    # inside a wikilink (either half) — the term has a card
    for w in re.finditer(r'\[\[[^\]]*\]\]', body):
        if w.start() <= m.start() and m.end() <= w.end():
            return True
    # inside *italics* — the definiendum
    for w in re.finditer(r'(?<!\*)\*(?!\*)[^*\n]+\*(?!\*)', body):
        if w.start() <= m.start() and m.end() <= w.end():
            return True
    # beside a relation symbol — the word is glossing it
    return bool(RELATION.search(body[max(0, m.start() - NEAR): m.end() + NEAR]))


bad = []
for f in pools.atoms():
    t = f.read_text()
    # Verbatim source text: the paper writes "morally" and "roughly" and that
    # is what it says. The rule exists for cards written here.
    if re.search(r'^verbatim:', t, re.M):
        continue
    h1 = re.search(r'^#\s+(.+)$', t, re.M)
    title = h1.group(1).lower() if h1 else ''
    for sec in re.finditer(r'## (Statement|Proof)\n(.*?)(?=\n## |\Z)', t, re.S):
        lines = [re.sub(r'^\s*>\s?', '', l) for l in sec.group(2).split('\n')]
        body = '\n'.join('' if l.lstrip().startswith('[!') else l for l in lines)
        for h in HEDGES:
            for m in re.finditer(r'\b' + h.replace(' ', r'\s+') + r'\b', body, re.I):
                if not licensed(body, m, title):
                    s = ' '.join(body[max(0, m.start() - 40): m.end() + 40].split())
                    bad.append((f.stem, sec.group(1), h, s))

for stem, sec, h, ctx in bad:
    print(f'{stem} ({sec}): bare "{h}" — …{ctx}…')
print(f'\nhedge lint: {len(bad)} unlicensed hedge(s)' if bad else 'hedge lint: clean')
sys.exit(1 if bad else 0)
