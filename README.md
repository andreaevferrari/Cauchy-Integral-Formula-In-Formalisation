# The Cauchy Integral Formula in Lean

This project formalises the Cauchy integral formula in Lean 4. It carries two
layers of the same mathematics:

* `CauchyIntegralFormula/` — the Lean library.
* `CauchyIntegralFormulaHypergraph/` — the statements as a hypergraph, one
  Markdown file per statement and one per declared dependency, readable as an
  Obsidian vault. See
  [its README](/CauchyIntegralFormulaHypergraph/README.md) for the card format.
  `bibliography/references/` holds one card per source.

Once the first build has run, the API documentation is at
[andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation](https://andreaevferrari.github.io/Cauchy-Integral-Formula-In-Formalisation/).

## Building

```bash
lake exe cache get     # fetch Mathlib's compiled oleans
lake build             # build the library
lake exe mk_all --module   # regenerate CauchyIntegralFormula.lean after adding files
```

## Contributing

Contributions go through pull requests against `main`. Please read
[CONTRIBUTING.md](/CONTRIBUTING.md) first.

## Acknowledgements

The repository's shape — its continuous integration in particular — follows
that of the
[Sphere Packing in Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
project, which is released under the Apache 2.0 licence. We thank the Mathlib
maintainers and the Lean community.
