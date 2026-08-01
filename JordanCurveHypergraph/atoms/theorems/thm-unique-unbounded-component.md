---
id: 0cf8d2c2f43b
status: formal
type: theorem
lean:
  - decl: JordanCurve.exists_unbounded_component
    module: JordanCurve.Curve.Basic
    line: 111
    state: proven
  - decl: JordanCurve.unbounded_component_unique
    module: JordanCurve.Curve.Basic
    line: 137
    state: proven
references:
  - "[[ref-maehara|Maehara 1984]]"
---

# Theorem — the complement of a curve has exactly one unbounded component

The easy half of the separation statement, and the half that needs no
geometry: a bounded set leaves everything far away in one piece.

## Statement

> [!theorem] One unbounded component
> Let $J$ be a [[def-jordan-curve|Jordan curve]]. Then $\mathbb{C} \setminus J$ has an unbounded [[def-connected|connected component]], and only one.

## Notes

> [!note]- Notes (click to expand)
> - $J$ is [[def-compact|compact]], so it lies in some disk; the complement of that disk is connected and unbounded, and every unbounded component must meet it.
> - Together with [[thm-exists-bounded-component]] and [[thm-bounded-component-unique]] this gives the count of two in [[thm-jordan-curve]].
