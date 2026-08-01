---
id: 5b389bb62c1c
type: definition
lean:
  - decl: JordanCurve.MaeharaConfiguration
    module: JordanCurve.Normalization.Configuration
    line: 49
    state: proven
references:
  - "[[ref-maehara|Maehara 1984]]"
---

# Definition — Maehara's configuration

Four points on the vertical axis and the midpoint between the middle two.
Every later claim is about that midpoint, and the four points are what pin it
in place.

## Statement

> [!definition] Maehara's configuration
> Let $J = J_N \cup J_S$ be a normalized [[def-jordan-curve|Jordan curve]] with its [[prop-arc-decomposition|arc decomposition]]. Its *configuration* consists of four points of $J$ on the vertical axis $x = 0$:
>
> | point | characterisation |
> |---|---|
> | $l$ | the highest point of $J$ on the axis; it lies on $J_N$ |
> | $m$ | the lowest point of $J_N$ on the axis |
> | $p$ | the highest point of $J_S$ on the axis at or below $m$ |
> | $q$ | the lowest point of $J_S$ on the axis |
>
> together with the *midpoint* $z_0$ of $m$ and $p$, which satisfies $q \le p < z_0 < m \le l$ in height.

## Notes

> [!note]- Notes (click to expand)
> - Each point exists because the relevant set is compact and non-empty — the second needing [[thm-crossing-lemma]] to see that the axis meets each arc at all.
> - The strict inequalities $p < z_0 < m$ are what put $z_0$ off the curve: a point of $J$ on the axis strictly between $m$ and $p$ would contradict the extremality of one of them.
