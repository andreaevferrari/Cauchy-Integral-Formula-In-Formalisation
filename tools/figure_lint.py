#!/usr/bin/env python3
r"""figure_lint.py — a tikz block that will not compile renders as a broken icon.

Obsidian's TikZJax is a small LaTeX, not a LaTeX installation, and it fails
silently: a missing package or an unsupported construct produces no message,
only a broken-image glyph where the figure should be. Nothing else in this
toolchain can see that, so a figure can sit wrong in a card indefinitely.

Two failure modes, both met in practice.

  * A symbol from a package the block never loaded. $\lesssim$ and
    $\lessapprox$ are amssymb; a block declaring only tikz shows nothing at
    all, not a figure with two missing glyphs.
  * A construct TikZJax does not carry. The plotting machinery is the one to
    watch — `plot`, `domain=`, `samples`, and the pgf math functions that go
    with them. Compute the points and emit a polyline instead; a curve through
    twenty-five explicit coordinates uses nothing beyond \draw.

The unsupported list is what has actually been tried, not a guess at TikZJax's
internals. Add to it when a figure breaks, with the construct that broke it.

Fatal. Usage: python3 tools/figure_lint.py
"""
import re, sys
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

NEEDS = {
    'amssymb': r'lesssim|lessapprox|gtrsim|gtrapprox|eqsim|mathbb|square|leqslant'
               r'|geqslant|varnothing|nmid|smallsetminus|subsetneq|thickapprox',
    'amsmath': r'tfrac|dfrac|operatorname|substack|boxed|xrightarrow|lvert|rvert',
}
UNSUPPORTED = {
    r'\bplot\b': 'plot — precompute the points and draw a polyline',
    r'\bdomain\s*=': 'domain= — belongs to plot',
    r'\bsamples\s*=': 'samples= — belongs to plot',
    r'\\addplot': 'pgfplots is not available',
    r'\busepackage\{pgfplots\}': 'pgfplots is not available',
    r'(?<!line )\bcap\s*=': 'bare cap= is a reserved key; use line cap=',
    r'\[\[': 'a wikilink in a caption — the figure is an image, so it draws as literal text',
    r'\bout\s*=(?!\s*-?\d)': 'out= outside a to-path is reserved',
}
BLOCK = re.compile(r'```tikz\n(.*?)```', re.S)
STMT = re.compile(r'## Statement\n(.*?)(?=\n## |\Z)', re.S)
SCALE = re.compile(r'\\(delta|rho)\b')

bad = []
for f in pools.files():
    text = f.read_text()
    stmt = STMT.search(text)
    for m in BLOCK.finditer(text):
        blk = '\n'.join(re.sub(r'^\s*>\s?', '', l) for l in m.group(1).split('\n'))
        # a figure that draws a scale onto a card whose statement has none has
        # invented the scale. def-lesssim is about an abstract parameter set;
        # an axis labelled log(1/delta) tells the reader the relation is about
        # a discretization, which is exactly what it is not.
        if stmt and SCALE.search(blk) and not SCALE.search(stmt.group(1)):
            bad.append((f.stem, 'the figure uses a scale the Statement never mentions'))
        for pkg, syms in NEEDS.items():
            hit = re.search(r'\\(' + syms + r')\b', blk)
            if hit and f'usepackage{{{pkg}}}' not in blk:
                bad.append((f.stem, f'\\{hit.group(1)} needs \\usepackage{{{pkg}}}'))
        for pat, why in UNSUPPORTED.items():
            if re.search(pat, blk):
                bad.append((f.stem, why))

for stem, why in bad:
    print(f'{stem}: {why}')
print(f'\nfigure lint: {len(bad)} broken figure(s)' if bad else 'figure lint: clean')
sys.exit(1 if bad else 0)
