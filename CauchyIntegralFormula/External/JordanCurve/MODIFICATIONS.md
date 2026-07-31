# Provenance and modifications

## Where this came from

These four files are a verbatim copy, modified only as listed below, of the
`jordan_curve` submission in

    https://github.com/rkirov/jordan_pick
    commit ad2aa1f637609c212210888b4ad9e926c30debb4
    path   submission/jordan_curve/Submission/
    licence Apache License 2.0 (LICENSE beside this file)

It was submitted to the [lean-eval](https://github.com/leanprover/lean-eval)
formalization benchmark and is recorded as solved on the leaderboard, by
@rkirov, using Claude Opus 4.8 (2026-07-01) and Claude Fable 5 (2026-07-10).
The submission record describes the production as roughly a week of grinding
with minimal human intervention.

The mathematics is Maehara's 1984 proof of the Jordan curve theorem via the
Brouwer fixed point theorem, and it is the authors' work, not this
repository's. This repository vendors it; it did not prove it.

## What was changed

Nothing mathematical. Four mechanical edits, required for the files to build
as part of this library rather than as a benchmark submission:

1. **Module paths.** `import Submission.X` became
   `import CauchyIntegralFormula.External.JordanCurve.X`.
2. **`module` header.** This library uses Lean 4.31's module system, and a
   `module` file cannot import a non-`module` one. Each file gained `module`
   as its first line.
3. **`public import`.** The imports became `public import`, so that the
   declarations of one vendored file are visible to the next.
4. **`@[expose] public section`** after the imports of each file, which is
   what Mathlib itself does to make a module's declarations visible
   downstream. Without it the declarations exist but cannot be named.

One factual note, left in place rather than edited: the header comment of
`Root.lean` says the file "is a work-in-progress with `sorry`s". That is true
of the file's ancestor in the `JordanPick/` tree it was extracted from, and
false of this copy — see below.

## What was verified here

```
#print axioms JordanCurve.jordan_curve
#print axioms JordanCurve.Brouwer.brouwerFPT
#print axioms JordanCurve.exists_unbounded_component
#print axioms JordanCurve.unbounded_component_unique
#print axioms JordanCurve.step_A_exists_bounded
```

Each depends on exactly `propext`, `Classical.choice`, `Quot.sound` — the
three standard axioms of Lean's logic, and no `sorryAx`. In particular
`BrouwerFPT`, which the argument carries as an explicit interface, is
discharged by `JordanCurve.Brouwer.brouwerFPT` inside these files: the final
theorem is unconditional.

## What this repository uses it for

`thm-jordan-curve` in the hypergraph, which `def-inside-of-path` rests on:
"inside" is defined as the bounded component of the complement, so the card
needs the bounded/unbounded split and not only the count of two. The
benchmark statement gives the count; these declarations give the rest.
