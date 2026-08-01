---
id: 1f43c21bd236
status: formal
type: proposition
lean:
  - decl: JordanCurve.exists_arc_decomposition_of_curve
    module: JordanCurve.Normalization.Setup
    line: 187
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Proposition — the two ends of the diameter cut the curve into two arcs

The cut that makes the argument possible. Neither arc separates the plane
([[thm-arc-does-not-separate-plane]]); the curve does; the difference has to
come from how the two are glued, and the proof extracts it from exactly this
decomposition.

## Statement

> [!proposition] Arc decomposition
> Let $J$ be a normalized [[def-jordan-curve|Jordan curve]], so that $-1, 1 \in J$. Then $J = J_N \cup J_S$ where $J_N$ and $J_S$ are [[def-arc|arcs]] with
> $$
> J_N \cap J_S = \{-1, 1\},
> $$
> each joining $-1$ to $1$, and each with path-connected interior $J_\bullet \setminus \{-1, 1\}$.

## Notes

> [!note]- Notes (click to expand)
> - The two points are the ends of the normalized diameter, which is why normalization comes first: the cut points have to be *on* the curve, and the farthest pair supplies them.
> - Which arc is called northern is fixed by [[def-maehara-configuration]], through the requirement that the highest point of the curve on the vertical axis lie on it.
