#!/usr/bin/env python3
r"""Render lint for the vault (run from the vault root).

Checks every known family of tex→Obsidian rendering defects:
  1. unexpanded custom macros (needs a macro list; checks common leftovers)
  2. \overline/\underline followed by an unbraced \mathit argument
  3. unescaped '[Word: ... ]' spans that Markdown may parse as links
  4. unbalanced braces inside display-math blocks (escaped braces excluded)
  5. inline math split across line breaks (odd unescaped $ count per line)
  6. whitespace hugging the inside of inline $ delimiters
  7. a display block too short to deserve one (curated pool)
  8. a Statement callout whose type does not match the card's `type:`
Exit code 1 if any offender is found. Usage: python3 tools/render_lint.py
"""
import pathlib, re, sys
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
bad = []      # in the curated layers: these fail the build
pool = []     # in the raw pool: reported, never fatal — raw material is never
              # polished in place, so a defect there is a note for whoever
              # graduates the card, not a gate on everyone else.

def note(f, msg):
    """File a defect against the layer it belongs to."""
    (pool if pools.pool_of(f) in pools.RAW else bad).append((f, msg))

COMMON_MACROS = [r'\\Ar(?![a-zA-Z])', r'\\Cee(?![a-zA-Z])', r'\\Zee(?![a-zA-Z])',
                 r'\\AAl(?![a-zA-Z])', r'\\eps(?![a-zA-Z])', r'\\btu(?![a-zA-Z])',
                 # package macros neither KaTeX nor Obsidian's MathJax defines:
                 # they render as red literal text. esint/mathtools averaged
                 # integrals are the ones that keep slipping in — write the
                 # fraction out instead.
                 r'\\fint(?![a-zA-Z])', r'\\avint(?![a-zA-Z])',
                 r'\\dashint(?![a-zA-Z])', r'\\Xint(?![a-zA-Z])',
                 r'\\Aboxed(?![a-zA-Z])', r'\\shortintertext(?![a-zA-Z])']

def single_dollar_count(s):
    return s.replace("\\$", "").replace("$$", "").count("$")

for f in sorted(V.rglob("*.md")):
    # `.lake/` is Lake's package store: thousands of markdown files belonging
    # to Mathlib and its dependencies. Linting them would make this check red
    # forever in a vault that also carries a Lean project.
    if ".obsidian" in str(f) or "/tools/" in str(f) or "/.lake/" in str(f):
        continue
    text = f.read_text()
    # (1) leftover macros. Inline code spans are excluded: a macro inside
    # backticks is being named — the notation file lists the source's own
    # \newcommand names that way — rather than left unexpanded.
    prose = re.sub(r'`[^`\n]*`', '', text)
    for pat in COMMON_MACROS:
        if re.search(pat, prose):
            note(f, f"unexpanded macro {pat}")
    # (2) \overline\mathit without braces
    if re.search(r'\\(overline|underline)\\mathit\{', text):
        note(f, "unbraced \\overline\\mathit group")
    # (2b) unclosed \mathit{word\ \}
    if re.search(r'\\mathit\{\w+[\\ ]*\\\}', text):
        note(f, "unclosed \\mathit group (escaped brace)")
    # (3) risky bracketed spans like [Proof: (unescaped)
    for m in re.finditer(r'(?<!\\)(?<!\[)\[(?!\[)([A-Z][a-z]+:)', text):
        note(f, f"unescaped bracket span {m.group(0)!r}")
    # (4) brace balance inside $$ blocks
    for m in re.finditer(r'\$\$(.*?)\$\$', text, re.S):
        s = re.sub(r'\\[{}]', '', m.group(1))
        if s.count('{') != s.count('}'):
            note(f, f"brace imbalance in display block ({s.count('{') - s.count('}'):+d})")
    # (5)+(6): per line, outside display blocks and fenced code blocks
    in_disp = False
    in_fence = False
    for n, ln in enumerate(text.splitlines(), 1):
        s = ln.strip().lstrip("> ").strip()
        if s.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if s == "$$":
            in_disp = not in_disp
            continue
        if in_disp or "$$" in ln:
            continue
        ln = re.sub(r'`[^`]*`', '', ln)  # inline code spans are not math
        if single_dollar_count(ln) % 2 == 1:
            note(f, f"line {n}: inline math split across lines (odd $ count)")
        parts = re.split(r'(?<!\\)\$', ln)
        for j in range(1, len(parts) - 1, 2):
            if parts[j] != parts[j].strip() and parts[j].strip():
                note(f, f"line {n}: whitespace inside inline $ delimiters")

# a wikilink alias must contain no math: $...$ inside an alias renders raw
# (clean pool only — the raw pool is never polished in place)
ALIAS_MATH = re.compile(r'\[\[[^\]|]+\|[^\]]*\$')
# a wikilink nested inside another wikilink's alias renders broken:
# [[a|... [[b|c]] ...]] — Obsidian cannot parse the inner link
NESTED_LINK = re.compile(r'\[\[[^\]]*\[\[')
# a display block costs the reader a paragraph of vertical space, so its body
# has to be worth one. $$Y(V) \subseteq V$$ is not: two symbols and a relation
# read better inside the sentence that introduces them. The threshold is set
# well below anything real — the curated pool's 68 displays have a median body
# of eight times this — so a hit means a containment or an equality got
# promoted to a block, never that a formula is merely compact.
SHORT_DISPLAY = 22

# The Statement callout carries the card's kind, and a CSS snippet colours it
# by that kind. So the callout type has to equal `type:` — a colour that says
# lemma over a definition is worse than no colour at all. Neither the id nor
# the export sees the header: assign_ids.py and vault-export.mjs both drop it
# by pattern, so this is free to fix and easy to let drift.
STATEMENT_CALLOUT = re.compile(r'## Statement\n\n?>\s*\[!([a-z]+)\]')
TYPE = re.compile(r'^type:\s*(\w+)', re.M)
for f in pools.atoms():
    text = f.read_text()
    kind, declared = STATEMENT_CALLOUT.search(text), TYPE.search(text)
    if kind and declared and kind.group(1) != declared.group(1):
        note(f, f"Statement callout is [!{kind.group(1)}] on a {declared.group(1)} card")

for f in pools.files():
    for m in re.finditer(r'\$\$(.+?)\$\$', f.read_text(), re.S):
        body = ' '.join(m.group(1).replace('>', ' ').split())
        if len(body) <= SHORT_DISPLAY:
            note(f, f"display block too short to be one: $${body}$$")

    for n, ln in enumerate(f.read_text().splitlines(), 1):
        if ALIAS_MATH.search(ln):
            note(f, f"line {n}: math inside a wikilink alias (put the link on a plain word)")
        if NESTED_LINK.search(ln):
            note(f, f"line {n}: nested wikilink [[..[[..]]..]] (links cannot nest)")

if pool:
    print(f"raw pool: {len(pool)} defect(s) — raw material, not a gate:")
    for f, msg in pool[:20]:
        print(f"  {f.relative_to(V)}: {msg}")
    print()

if bad:
    for f, msg in bad[:60]:
        print(f"{f.relative_to(V)}: {msg}")
    print(f"\n{len(bad)} offender(s).")
    sys.exit(1)
print("render lint: clean")
