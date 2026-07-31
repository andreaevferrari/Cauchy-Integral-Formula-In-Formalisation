#!/usr/bin/env python3
r"""notation_lint.py — the notation table is normative; check that it is (advisory).

`notation.md` is declared normative by rules.md § 5: one name and one symbol
per concept, registered there at graduation time. Nothing read it until now,
which is fine for a topic written in an afternoon and not fine for a book
whose preliminaries and main text are written months apart. Drift is silent —
`\Delta_{\max}` beside `\Delta_{max}`, `C_{F}` beside `C_F` — and it renders
identically, so no other linter can see it.

Three checks. The first two are about the table's completeness, the third
about whether it is telling the truth.

Reports every macro used inside maths in a Statement or Proof that does not
appear anywhere in `notation.md`. Two kinds of hit, and both are worth seeing:

  * a symbol genuinely not registered — the debt rules.md § 4 is about;
  * a spelling that differs from the registered one — the same concept written
    two ways, which is the failure the table exists to prevent.

Grammar is not vocabulary: \frac, \left, \sum and their kind are filtered, so
what remains is the mathematics a reader has to look up.

Then, fatally: **a row naming a card must name a card whose Statement contains
that symbol.** This is the failure the table is most prone to, because a row
is written once and the cards move afterwards. Four wrong rows were found by
hand in one evening — lambda pointing at the shading card rather than the
shading-density card, Delta_max at convex-density rather than maximal-density,
W[K] bundled into a row about something else, and the dimensions row pointing
at delta-tube while def-dimensions is the card whose own callout header is
that symbol. Each would have sent a reader to a card that does not define what
they looked up, and an automatic keyword substitution driven by this table
would have inserted every one of them as a link.

A row whose symbol appears only in the card's Notes counts as a miss, and
should: a definition consumed by someone else's Statement does not belong in
commentary. That is how the angle-of-intersection card came to exist.

Only rows naming a symbol are checked. A table may also list notions by name —
those belong to term_lint, and matching an English phrase against Statement
text produces noise rather than findings.

Usage: python3 tools/notation_lint.py
"""
import re, sys, pathlib, collections
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

# Structural TeX: it shapes a formula, it is not a thing to be defined.
GRAMMAR = {
    'frac', 'tfrac', 'dfrac', 'left', 'right', 'big', 'Big', 'bigg', 'Bigg',
    'sum', 'prod', 'int', 'lim', 'inf', 'sup', 'max', 'min', 'log', 'exp',
    'sqrt', 'cdot', 'cdots', 'dots', 'ldots', 'quad', 'qquad', 'text', 'textstyle',
    'displaystyle', 'mathrm', 'mathbb', 'mathcal', 'mathbf', 'operatorname',
    'le', 'ge', 'leq', 'geq', 'ne', 'neq', 'in', 'notin', 'subset', 'subseteq',
    'supseteq', 'cup', 'cap', 'setminus', 'emptyset', 'to', 'mapsto', 'times',
    'lesssim', 'gtrsim', 'lessapprox', 'gtrapprox', 'eqsim', 'approx', 'sim',
    'll', 'gg', 'pm', 'circ', 'square', 'colon', 'mid', 'lvert', 'rvert',
    'langle', 'rangle', 'lceil', 'rceil', 'lfloor', 'rfloor', 'partial',
    'forall', 'exists', 'implies', 'iff', 'land', 'lor', 'neg', 'bigcup',
    'bigcap', 'bigsqcup', 'sqcup', 'begin', 'end', 'label', 'ref', 'qquad',
    'mathbin', 'mathopen', 'mathclose', 'nonumber', 'hspace', 'vspace',
    # decoration and limits: they modify a symbol, they are not one
    'tilde', 'hat', 'bar', 'overline', 'underline', 'widetilde', 'widehat',
    'limsup', 'liminf', 'infty', 'varnothing', 'mathbf', 'mathsf', 'mathit',
    'arg', 'det', 'ker', 'dim', 'arcsin', 'arccos', 'arctan', 'sin', 'cos', 'tan',
    'substack', 'Vert', 'lVert', 'rVert', 'textrm', 'phantom', 'qedhere',
}

MATH = re.compile(r'\$\$(.+?)\$\$|\$(.+?)\$', re.S)
MACRO = re.compile(r'\\([a-zA-Z]+)')


def math_spans(text):
    for m in MATH.finditer(text):
        yield m.group(1) or m.group(2) or ''


def main():
    table = (pools.CLEAN[0] / 'notation.md')
    if not table.exists():
        sys.exit(f'no notation.md in {pools.CLEAN[0].name}')
    declared = table.read_text()

    used = collections.defaultdict(set)      # macro -> cards using it
    for f in pools.atoms():
        t = f.read_text()
        stmt = re.search(r'## Statement\n(.*?)(?=\n## Notes|\Z)', t, re.S)
        if not stmt:
            continue
        for chunk in math_spans(stmt.group(1)):
            for name in MACRO.findall(chunk):
                if name not in GRAMMAR:
                    used[name].add(f.stem)

    # A row's card must actually define the symbol the row names.
    rows = re.findall(r'^\|\s*(.+?)\s*\|\s*(.*?)\s*\|\s*\[\[([a-z0-9-]+)\]\]\s*\|', declared, re.M)
    statements = {}
    for f in pools.atoms():
        s = re.search(r'## Statement\n(.*?)(?=\n## |\Z)', f.read_text(), re.S)
        statements[f.stem] = s.group(1) if s else ''
    # A row may point at a section of the narrative rather than at a card: the
    # source introduces some notation in running prose, and pointing at the
    # place it does so is the truthful target even though it is not a node.
    for f in (pools.V / 'topics').rglob('*.md'):
        statements[f.stem] = f.read_text()
    mispointed = []
    for sym, meaning, card in rows:
        # Only rows that name a symbol. A table may also carry rows whose first
        # column is an English name — those are checked by term_lint, not here,
        # and matching them against Statement text produces noise.
        # Every maths fragment in the cell, since a table may write a symbol
        # bare or wrapped in its name — `$K(\sigma)$` and `sectional curvature
        # $K(\sigma)$` are both rows about the same symbol.
        # A row is consistent if the card writes the symbol, or writes one the
        # meaning column names — which is how an alias row passes. `$\delta$-neck
        # | an $\epsilon$-neck with the finer parameter` points at the epsilon
        # card on purpose, and the card says epsilon.
        if '$' not in sym:
            continue          # a row naming a notion in words belongs to term_lint
        frags = [f.strip() for f in re.findall(r'\$([^$]+)\$', sym + ' ' + meaning) if f.strip()]
        if not frags:
            continue
        if card not in statements:
            mispointed.append((sym, card, 'no such card'))
        elif not any(f in statements[card] for f in frags):
            mispointed.append((sym, card, 'that card\'s Statement contains none of its symbols'))

    missing = {m: c for m, c in used.items() if f'\\{m}' not in declared}
    for m, cards in sorted(missing.items(), key=lambda kv: -len(kv[1])):
        shown = ', '.join(sorted(cards)[:3]) + (' …' if len(cards) > 3 else '')
        print(f'  \\{m:<20} {len(cards):>2} card(s): {shown}')
    print(f'\nnotation lint: {len(missing)} unregistered symbol(s) '
          f'of {len(used)} used — advisory, judge by hand')

    for sym, card, why in mispointed:
        print(f'  MISPOINTED  {sym}  ->  {card}: {why}')
    if mispointed:
        print(f'\n{len(mispointed)} row(s) of {len(rows)} name the wrong card.')
    sys.exit(1 if mispointed else 0)


if __name__ == '__main__':
    main()
