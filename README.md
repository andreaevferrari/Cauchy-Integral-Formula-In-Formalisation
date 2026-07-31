# The Cauchy Integral Formula in Lean

This project carries two layers of the same mathematics:

* `CauchyIntegralFormula/` — the Lean library.
* `CauchyIntegralFormulaHypergraph/` — the statements as a hypergraph, one
  Markdown file per statement and one per declared dependency, readable as an
  Obsidian vault. [`rules.md`](/CauchyIntegralFormulaHypergraph/rules.md) says
  what a card is, what an edge means and what may appear where;
  [`notation.md`](/CauchyIntegralFormulaHypergraph/notation.md) is normative
  for symbols. `bibliography/references/` holds one card per source, and the
  sources themselves live untracked in `pipeline/sources/`.

The six numbered files at the root are the exposition: prose that connects the
cards, which render in place as embeds. Start at
[`00-introduction.md`](/00-introduction.md).

Once the first build has run, the API documentation is at
[andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation](https://andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation/).

## Building the Lean library

```bash
lake exe cache get         # fetch Mathlib's compiled oleans
lake build
lake exe mk_all --module   # regenerate CauchyIntegralFormula.lean after adding files
```

CI checks that the root import file is up to date, and rejects a bare
`import Mathlib` or a `#check` left at the top level.

## Working on the hypergraph

Write the card by hand, wire nothing by hand: `gen_edges.py` derives the edge
files from the links the text already carries, and `assign_ids.py` addresses
every card by the hash of its own statement.

```bash
python3 tools/gen_edges.py     # rebuild edges/ from the links in the cards
python3 tools/assign_ids.py    # ids (idempotent)
python3 tools/render_lint.py   # tex → Obsidian rendering
python3 tools/noise_lint.py    # no bibliographic noise inside the mathematics
python3 tools/edge_lint.py     # edges mirror the text, exactly
python3 tools/bib_lint.py      # every reference card has a label and an entry
```

All five must print clean. `python3 tools/frontier.py` is the one to run when
deciding what to do next: it prints the proof debts and a layering of the
cards, leaves first, in the order a Lean skeleton would be written.

A pull request that adds mathematics should touch both layers — the Lean
declaration, and the card whose `lean:` field names it.

## Acknowledgements

We thank the Mathlib maintainers and the Lean community.
