---
id: b4b5a6dc8ce0
status: formal
type: theorem
lean:
  - decl: JordanCurve.component_boundary_eq
    module: JordanCurve.Curve.Separation
    line: 226
    state: proven
references:
  - "[[ref-maehara|Maehara 1984]]"
---

# Theorem — the curve is the boundary of each component of its complement

The third clause of the separation statement, and the one that says the two
components really are separated *by the curve* rather than by some part of
it.

## Statement

> [!theorem] Each component has the curve as boundary
> Let $J$ be a [[def-jordan-curve|Jordan curve]] whose complement is disconnected, and let $U$ be a [[def-connected|connected component]] of $\mathbb{C} \setminus J$. Then $\partial U = J$.

## Notes

> [!note]- Notes (click to expand)
> - The inclusion $\partial U \subseteq J$ is immediate. For the reverse: if some point of $J$ were not on $\partial U$, the boundary would sit inside a proper sub-[[def-arc|arc]] of $J$, and [[thm-arc-does-not-separate-plane]] applied to that arc would make the complement connected after all.
