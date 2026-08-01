---
id: c974d7f51683
status: formal
type: theorem
lean:
  - decl: JordanCurve.jordan_curve
    module: JordanCurve.Main
    line: 57
    state: proven
  - decl: JordanCurve.exists_unbounded_component
    module: JordanCurve.Curve.Basic
    line: 111
    state: proven
  - decl: JordanCurve.unbounded_component_unique
    module: JordanCurve.Curve.Basic
    line: 137
    state: proven
  - decl: JordanCurve.exists_bounded_component
    module: JordanCurve.Component.Bounded
    line: 347
    state: proven
  - decl: JordanCurve.component_boundary_eq
    module: JordanCurve.Curve.Separation
    line: 226
    state: proven
references:
  - "[[ref-beck|Beck et al., §4.4 — assumed there, not proved]]"
---

# Theorem — a simple closed path separates the plane

What gives the word "inside" a meaning: without it the hypothesis "$w$ is
inside $\gamma$" is not a hypothesis about anything. The source assumes it.
This network does not have to, because a formal proof exists.

## Statement

> [!theorem] Jordan curve theorem
> Let $J$ be a [[def-jordan-curve|Jordan curve]]. Then $\mathbb{C} \setminus J$ has exactly two [[def-connected|connected components]], one bounded and one unbounded, and $J$ is the boundary of each.

## Notes

> [!note]- Notes (click to expand)
> - It is one of the earliest substantial theorems of topology, and every known proof is long out of proportion to how obvious the statement looks. There is no proof written here, and no prose proof is planned: the formal one is the proof this network stands on.
> - The formal counterpart is not Mathlib's — Mathlib has no Jordan curve theorem, and every declaration there whose name contains `Jordan` belongs to Jordan–Hölder, Jordan algebras or the Jordan decomposition of a measure. It is vendored into this repository under `CauchyIntegralFormula/JordanCurve/`, with its provenance and the four mechanical edits recorded in `PROVENANCE.md` beside it. The mathematics is Maehara's proof via the Brouwer fixed point theorem, and it is not this repository's work.
> - The five declarations together cover the three clauses of the statement. `jordan_curve` gives the count of two and is unconditional. The other four carry `BrouwerFPT` as an explicit hypothesis, which `JordanCurve.Brouwer.brouwerFPT` discharges in the same development — so the conditionality is bookkeeping, not a gap.
> - The three clauses are assembled from [[thm-exists-bounded-component]], [[thm-bounded-component-unique]] and [[thm-unique-unbounded-component]], with the boundary clause from [[thm-component-boundary-is-curve]]. All four rest on [[thm-crossing-lemma]] and through it on [[thm-brouwer-fixed-point]].
> - The count of two does not by itself say which component is bounded, and [[def-inside-of-path]] needs exactly that. `exists_unbounded_component` and `unbounded_component_unique` give the unbounded one and its uniqueness, `exists_bounded_component` the bounded one, and `component_boundary_eq` the boundary clause.
