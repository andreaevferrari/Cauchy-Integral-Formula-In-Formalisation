#!/usr/bin/env python3
r"""Where the cards live — and everything else that is about THIS vault
rather than about the method. Every tool reads this file rather than naming a
directory, so instantiating the template is an edit here instead of an edit in
thirteen scripts.

This vault has one pool and no raw pool: its cards are written by hand from
the source rather than cut mechanically, so there is nothing to graduate out
of. `RAW` staying empty is what makes `status: open` unreachable here — a
card is either `debt` (no proof) or `proved`.
"""
import pathlib

V = pathlib.Path(__file__).resolve().parent.parent

#: Curated pools, in the order tools should report them.
CLEAN = [V / 'JordanCurveHypergraph']

#: Raw material, mechanically cut from sources. Empty: see the module docstring.
RAW = []

ALL = CLEAN + RAW

#: The card the network is grown from.
ROOT = 'thm-jordan-curve'

#: Surnames that must not appear in a Statement or Proof. Mathematics is
#: attributed in Notes and in the `references:` frontmatter, never in the
#: statement itself. These are the source's authors — the names this vault is
#: tempted to write. A name that is part of a result's name (Jordan, Brouwer,
#: Maehara) is not an attribution and is not listed.
AUTHORS = ['Marchesi', 'Pixton', 'Sabalka']


def atoms(pools=None):
    """Every atom file in the given pools (curated ones by default)."""
    for p in (pools if pools is not None else CLEAN):
        d = p / 'atoms'
        if d.exists():
            yield from sorted(d.rglob('*.md'))


def edges(pools=None):
    """Every edge file in the given pools (curated ones by default)."""
    for p in (pools if pools is not None else CLEAN):
        d = p / 'edges'
        if d.exists():
            yield from sorted(d.rglob('*.md'))


def files(pools=None):
    """Every markdown file in the given pools."""
    for p in (pools if pools is not None else CLEAN):
        if p.exists():
            yield from sorted(p.rglob('*.md'))


def pool_of(path):
    """Which pool a file sits in, or None."""
    path = pathlib.Path(path).resolve()
    for p in ALL:
        if str(path).startswith(str(p.resolve()) + '/'):
            return p
    return None

_STOP = {'a', 'an', 'the', 'of', 'and', 'or', 'its', 'for', 'under', 'with', 'to', 'in'}
_TAIL = __import__('re').compile(r'\s+(?:of|inside|in|for|on|under|between|from)\s+.*$')


def phrases_of(title):
    """Every term a definition card claims, from the text after its em-dash.

    A title naming several notions is split on commas and `and`, and each part
    is offered in singular and plural.

    Deliberately NOT reduced to a head noun. "The dimensions of a convex set"
    would give "dimensions", which then fires inside "Hausdorff dimension",
    "three dimensions" and every other ordinary use of the word — English is
    ambiguous there and no rule recovers it. A checker that reports seventy
    guesses is worse than one that reports five facts.
    """
    import re
    core = title.split('\u2014')[-1].strip().lower()
    core = re.sub(r'\(.*?\)', '', core)
    out = set()
    for part in re.split(r',| and ', core):
        part = part.strip().strip('.')
        part = re.sub(r'^(?:a|an|the) ', '', part)
        if not part or part in _STOP or len(part) < 4:
            continue
        out.add(part)
        out.add(part[:-1] if part.endswith('s') else part + 's')
    return out


def definition_terms(pools=None):
    """term -> the definition card that claims it.

    A phrase two cards both claim is dropped from both. An ambiguous term
    cannot be checked mechanically — reporting it against either card would
    be a guess — and head-noun extraction manufactures such collisions, so
    the rule pays for itself.
    """
    import re, collections
    claims = collections.defaultdict(set)
    for f in atoms(pools):
        if f.parent.name != 'definitions':
            continue
        h = re.search(r'^#\s+.*?\u2014\s*(.+)$', f.read_text(), re.M)
        if not h:
            continue
        for ph in phrases_of(h.group(1)):
            claims[ph].add(f.stem)
    return {ph: next(iter(s)) for ph, s in claims.items() if len(s) == 1}
