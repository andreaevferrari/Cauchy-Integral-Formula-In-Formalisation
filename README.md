# The Jordan Curve Theorem

A loop in the plane that does not cross itself divides the plane into an inside and an outside. This repository carries that theorem in three layers, and they correspond:

* `JordanCurve/` — the Lean library. Maehara's proof via the Brouwer fixed
  point theorem, `sorry`-free, and audited: every theorem the cards name
  depends on exactly `propext`, `Classical.choice` and `Quot.sound`. Mathlib does not have this theorem.
* `JordanCurveHypergraph/` — the statements as a hypergraph, one Markdown
  file per statement and one per declared dependency, readable as an Obsidian
  vault. [`rules.md`](/JordanCurveHypergraph/rules.md) says what a card is,
  what an edge means and what may appear where;
  [`notation.md`](/JordanCurveHypergraph/notation.md) is normative for
  symbols. Cards name their formal counterpart in a `lean:` field.
* The numbered files at the root are the exposition: prose that connects the
  cards, which render in place as embeds. Start at
  [`00-introduction.md`](/00-introduction.md).

There are no proof debts. `python3 tools/frontier.py` says so, and would say
otherwise if a statement were being assumed.

Once the first build has run, the API documentation is at
[andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation](https://andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation/).

## Building the Lean library

```bash
lake exe cache get         # fetch Mathlib's compiled oleans
lake build
lake exe jordan-audit      # public API present, and no axiom beyond the three
lake exe mk_all --module   # regenerate JordanCurve.lean after adding files
lake build JordanCurve:docs
```

`jordan-audit` runs in CI. It is the check that matters: `lake build`
succeeding proves the files elaborate, not that the theorems rest on nothing.
`JordanCurve/Anchor.lean` guards the other failure mode — it restates the
theorem independently and stops compiling if anything it passes through is
weakened. It is never edited to make it compile.

CI also rejects a bare `import Mathlib` and a top-level `#check`.

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
python3 tools/lean_lint.py     # every `lean:` declaration still exists
```

All six must print clean. `python3 tools/frontier.py` prints the proof debts
and a layering of the cards, leaves first, in the order a Lean skeleton would
be written.

A card names a mathematical statement, not a Lean declaration: the plumbing
that carries the argument in Lean — coordinate projections, path
concatenation, the parametrisation of a segment — has no card, and is marked
`**Eng.**` in the library instead.

## References

The mathematics is Maehara's 1984 proof via the Brouwer fixed point theorem.
The development started from the `jordan_curve` problem of the
[lean-eval](https://lean-lang.org/eval/problems/jordan_curve/) benchmark and
one of its published solutions;
[`JordanCurve/PROVENANCE.md`](/JordanCurve/PROVENANCE.md) names both and lists
everything that was changed here.

## Acknowledgements

We thank the Mathlib maintainers and the Lean community.
