---
id: 319465ebee0e
status: formal
type: theorem
lean:
  - decl: JordanCurve.exists_bounded_component
    module: JordanCurve.Component.Bounded
    line: 347
    state: proven
references:
  - "[[ref-maehara|Maehara 1984]]"
---

# Theorem — the complement of a Jordan curve has a bounded component

Maehara's Step A, and the half of the separation statement that is not
obvious: a curve with no smoothness at all still encloses something.

## Statement

> [!theorem] A bounded component exists
> Let $J$ be a [[def-jordan-curve|Jordan curve]]. Then some [[def-connected|connected component]] of $\mathbb{C} \setminus J$ is bounded.

## Notes

> [!note]- Notes (click to expand)
> - The witness is the midpoint $z_0$ of [[def-maehara-configuration]]. Suppose its component were unbounded. Then a path from $z_0$ escapes the rectangle, and its first exit point lies on the boundary — above the axis or below it.
> - Say below. Concatenate five pieces: along the southern boundary of the rectangle to the exit point, back along the escaping path to $z_0$, up the axis to $m$, on to $l$, and out to the top edge. The result runs from the bottom edge to the top edge and misses $J_S$ entirely — which [[thm-crossing-lemma]] forbids, since $J_S$ joins the left edge to the right edge.
> - The case above the axis is the same argument reflected, missing $J_N$ instead.
