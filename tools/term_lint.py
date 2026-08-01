#!/usr/bin/env python3
r"""term_lint.py — the half-linked-term detector (advisory).

A long Statement or Proof often links a concept at its first occurrence
and then uses the same word bare later — or a consumer links one of a
definition card's terms but not another. edge_lint cannot see this: the
edge already exists from the linked occurrence. This linter lists every
place where a definition card's term appears as plain prose inside a
Statement/Proof that has NO wikilink on it.

Advisory only: it prints candidates and exits 0. Some bare repeats are
fine (a word's fifth mention in one proof). Human decides; this just
surfaces the list so nobody has to read every card by eye.

Usage: python3 tools/term_lint.py [--card <stem>]
"""
import re, sys, pathlib
import sys as _sys; _sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent)); import pools

V = pathlib.Path(__file__).resolve().parent.parent
# definitions and atoms come from every curated pool (tools/pools.py)

# ---- build the term -> card map from definition-card H1 titles ----
# "# Definition — canonical neighborhood" -> phrases {"canonical neighborhood"}
STOP = {'a','an','the','of','and','or','its','for','under','with','to'}
def phrases_of(title):
    """Every term a definition card claims, from its H1.

    A card often defines more than one thing — "delta-tube, and the dimensions
    of a convex set" defines two — so the title is split on commas and on
    " and ". Taking it whole, as this once did, produced a phrase no prose
    would ever contain, and the card's terms were never checked at all.
    """
    core = title.split('—')[-1].strip().lower()
    core = re.sub(r'\(.*?\)', '', core)
    out = set()
    for part in re.split(r',| and ', core):
        part = part.strip().strip('.')
        # a leading article survives the split: "the dimensions of a convex set"
        part = re.sub(r'^(?:a|an|the) ', '', part)
        if not part or part in STOP:
            continue
        out.add(part)
        out.add(part[:-1] if part.endswith('s') else part + 's')
    return out


# Prose writes a Greek letter as maths and a title spells it out, so
# `$\delta$-tube` and `delta-tube` are the same term and must compare equal.
GREEK = re.compile(r'\$\\(alpha|beta|gamma|delta|epsilon|eta|theta|kappa|lambda|mu|nu|rho'
                   r'|sigma|tau|phi|chi|psi|omega|Delta|Gamma|Lambda|Sigma|Phi|Omega)\$')


def despair(text):
    """Text as the title spells it: $\\delta$-tube becomes delta-tube."""
    return GREEK.sub(lambda m: m.group(1).lower(), text)

term2card = {}
for f in (a for a in pools.atoms() if a.parent.name == 'definitions'):
    m = re.search(r'^#\s+.*?—\s*(.+)$', f.read_text(), re.M)
    if not m: continue
    for ph in phrases_of(m.group(1)):
        # longer phrases win; keep the most specific card per phrase
        term2card.setdefault(ph, f.stem)

# sort phrases longest-first so "canonical neighborhood" matches before "neighborhood"
phrases = sorted(term2card, key=len, reverse=True)

def sections(t):
    for name, pat in (('Statement', r'## Statement\n(.*?)(?=\n## Proof|\n## Notes|\n## References|\Z)'),
                      ('Proof', r'## Proof\n(.*?)(?=\n## Notes|\n## References|\Z)')):
        m = re.search(pat, t, re.S)
        if m: yield name, m.group(1), m.start(1)

def linked_spans(text):
    """Spans that already carry a link — and callout headers, which must not.

    A `> [!theorem] Kakeya sets of measure zero exist` line is the statement's
    title, not its prose: a wikilink there renders inside the callout chrome
    and reads as a mistake. `assign_ids.statement_body` already skips these
    lines for the same reason, so a term appearing only in a header is not a
    missing link.
    """
    spans = [(m.start(), m.end()) for m in re.finditer(r'\[\[[^\]]*\]\]', text)]
    spans += [(m.start(), m.end()) for m in re.finditer(r'^\s*>+\s*\[![a-z]+\].*$', text, re.M)]
    return spans

target = None
if len(sys.argv) == 3 and sys.argv[1] == '--card':
    target = sys.argv[2]

hits = 0
for f in pools.atoms():
    if target and f.stem != target: continue
    t = f.read_text()
    for sec, body, _ in sections(t):
        # Normalise once and index everything into the same string: despair()
        # changes the length, so spans taken from the raw body would not line up.
        body = despair(body)
        spans = linked_spans(body)
        low = body.lower()
        claimed = []   # (start, end) spans consumed by a longer phrase — suppress shorter ones inside
        for ph in phrases:                       # phrases are longest-first
            card = term2card[ph]
            if card == f.stem: continue          # a card need not link itself
            for m in re.finditer(r'(?<![a-z])' + re.escape(ph) + r'(?![a-z])', low):
                s, e = m.start(), m.end()
                if any(a <= s < b for a, b in spans): claimed.append((s, e)); continue   # inside a wikilink
                if any(a <= s < e <= b for a, b in claimed): continue                     # inside a longer phrase
                claimed.append((s, e))
                already = re.search(r'\[\[' + re.escape(card) + r'[\|\]]', body)
                note = ' (card linked elsewhere in section)' if already else ''
                print(f'{f.stem} [{sec}]: bare "{ph}" -> [[{card}]]{note}')
                hits += 1
                break  # one report per (card, section) is enough
print(f'\nterm lint: {hits} candidate(s) — advisory, review by hand')
sys.exit(0)
