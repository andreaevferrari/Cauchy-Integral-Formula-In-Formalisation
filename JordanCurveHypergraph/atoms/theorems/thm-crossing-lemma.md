---
id: 58eb2a3d4f73
status: formal
type: theorem
lean:
  - decl: JordanCurve.transversal_paths_meet_in_rectangle
    module: JordanCurve.Crossing
    line: 29
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Theorem — two transversal paths in a rectangle must meet

The workhorse. Everything the separation argument proves about which points
lie inside which component is proved by exhibiting two paths across a
rectangle and concluding that they cross.

## Statement

> [!theorem] Crossing lemma
> Let $R = [a,b] \times [c,d]$ be a rectangle and let $h, v : [-1,1] \to R$ be [[def-continuity|continuous]], with $h$ running from the left edge to the right edge and $v$ from the bottom edge to the top edge. Then $h$ and $v$ meet: there are $s, t$ with $h(s) = v(t)$.

## Notes

> [!note]- Notes (click to expand)
> - It follows from [[thm-brouwer-fixed-point]] by an explicit map of the square to its boundary: if the two paths missed each other, normalising their difference would give a fixed-point-free self-map of the square.
> - "Transversal" here is only about which edges the paths join, not about angles — the paths may be as wild as continuity allows.
