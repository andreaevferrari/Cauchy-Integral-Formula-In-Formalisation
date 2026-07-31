# Contributing

Thank you for your interest in contributing. This guide describes how to work
on the project.

## How to Contribute

Contributions are made through GitHub pull requests. Tasks are posted as GitHub
issues; comment on an issue to say you are taking it, so that two people do not
write the same proof twice.

### 1. Setting up

1. Install Lean via [elan](https://leanprover-community.github.io/get_started.html).
2. Clone the repository and fetch Mathlib's compiled files:

   ```bash
   git clone https://github.com/andreaevferrari/Cauchy-Integral-Formula-In-Formalisation.git
   cd Cauchy-Integral-Formula-In-Formalisation
   lake exe cache get
   lake build
   ```

### 2. Working on a task

Create a branch off `main`. After adding new `.lean` files, run

```bash
lake exe mk_all --module
```

to regenerate the root import file `CauchyIntegralFormula.lean`; CI checks that
it is up to date.

Two things CI will reject: a bare `import Mathlib`, and a `#check` left at the
top level of a file.

### 3. Keeping the two layers in step

A statement lives in two places, and a PR that adds mathematics should touch
both:

- **Lean** — the declaration, in `CauchyIntegralFormula/`.
- **Hypergraph** — the card in `CauchyIntegralFormulaHypergraph/atoms/`, whose
  `lean:` field names the declaration. Its format and its four rules are in
  [the pool's README](/CauchyIntegralFormulaHypergraph/README.md).

Formalising something whose card already exists needs only the first, plus the
card's `lean:` and `formalized:` fields.

### 4. Submitting a pull request

Open a PR from your branch against `main`, and say in the body which issue it
closes. A maintainer will review it; PRs need an approving review and green CI
before they can be merged.

## Style

`.vscode/settings.json` carries the settings the project assumes: two-space
indentation, a 100-character ruler, LF endings, a final newline, no trailing
whitespace. Otherwise, follow the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html).
