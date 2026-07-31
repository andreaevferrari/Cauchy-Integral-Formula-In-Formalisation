---
id: 3f71a80ca4eb
status: formal
type: theorem
lean:
  - decl: JordanCurve.jordan_curve
    module: CauchyIntegralFormula.External.JordanCurve.Root
    line: 2565
    state: proven
  - decl: JordanCurve.exists_unbounded_component
    module: CauchyIntegralFormula.External.JordanCurve.Root
    line: 310
    state: proven
  - decl: JordanCurve.unbounded_component_unique
    module: CauchyIntegralFormula.External.JordanCurve.Root
    line: 336
    state: proven
  - decl: JordanCurve.step_A_exists_bounded
    module: CauchyIntegralFormula.External.JordanCurve.Root
    line: 1973
    state: proven
  - decl: JordanCurve.component_boundary_eq
    module: CauchyIntegralFormula.External.JordanCurve.Root
    line: 594
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
> Let $\gamma$ be a simple closed path in $\mathbb{C}$. Then $\mathbb{C} \setminus \gamma$ has exactly two [[def-connected|connected components]], one bounded and one unbounded, and $\gamma$ is the boundary of each.

## Notes

> [!note]- Notes (click to expand)
> - It is one of the earliest substantial theorems of topology, and every known proof is long out of proportion to how obvious the statement looks. There is no proof written here, and no prose proof is planned: the formal one is the proof this network stands on.
> - The formal counterpart is not Mathlib's — Mathlib has no Jordan curve theorem, and every declaration there whose name contains `Jordan` belongs to Jordan–Hölder, Jordan algebras or the Jordan decomposition of a measure. It is vendored into this repository under `CauchyIntegralFormula/External/JordanCurve/`, with its provenance and the four mechanical edits recorded in `MODIFICATIONS.md` beside it. The mathematics is Maehara's proof via the Brouwer fixed point theorem, and it is not this repository's work.
> - The five declarations together cover the three clauses of the statement. `jordan_curve` gives the count of two and is unconditional. The other four carry `BrouwerFPT` as an explicit hypothesis, which `JordanCurve.Brouwer.brouwerFPT` discharges in the same development — so the conditionality is bookkeeping, not a gap.
> - The count of two does not by itself say which component is bounded, and `[[def-inside-of-path]]` needs exactly that. `exists_unbounded_component` and `unbounded_component_unique` give the unbounded one and its uniqueness, `step_A_exists_bounded` the bounded one, and `component_boundary_eq` the boundary clause.
