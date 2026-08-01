---
id: abe709ff59e7
status: proved
type: proposition
lean:
  - decl: JordanCurve.exists_similarity_normalizing_farthest_pair
    module: JordanCurve.Normalization.Frame
    line: 142
    state: proven
  - decl: JordanCurve.normalized_subset_rectangle
    module: JordanCurve.Normalization.Setup
    line: 35
    state: proven
references:
  - "[[ref-maehara|Maehara 1984]]"
---

# Proposition — a similarity puts the farthest pair at ±1 and the curve in a rectangle

The step that turns a statement about an arbitrary curve into a statement
about a curve in a known box. Separation is invariant under a similarity, so
nothing is lost by moving the curve first.

## Statement

> [!proposition] Normalization
> Let $J$ be a [[def-jordan-curve|Jordan curve]]. There is a similarity $T$ of the plane such that $T(J)$ contains $-1$ and $1$, every two points of $T(J)$ are at distance at most $2$, and
> $$
> T(J) \subseteq [-1,1] \times [-2,2].
> $$

## Proof

> [!note]- Proof (click to expand)
> $J$ is [[def-compact|compact]], so the distance function attains its maximum on $J \times J$ at some pair $a \neq b$; that maximum is the diameter. A similarity carries $a \mapsto -1$ and $b \mapsto 1$ and scales every distance by $2 / \lvert a - b \rvert$, so the diameter of the image is $2$.
>
> For the rectangle: any $z$ in the image satisfies $|z+1| \le 2$ and $|z-1| \le 2$. Writing $z = x + iy$, these say $(x+1)^2 + y^2 \le 4$ and $(x-1)^2 + y^2 \le 4$. Subtracting gives $|x| \le 1$; adding gives $x^2 + y^2 \le 3$, hence $|y| \le 2$. $\square$
