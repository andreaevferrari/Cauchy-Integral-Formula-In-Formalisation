---
id: 90903b29a6b2
status: formal
type: theorem
lean:
  - decl: JordanCurve.arc_not_separates
    module: JordanCurve.Curve.Separation
    line: 36
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Theorem — an arc does not separate the plane

The contrast that makes the Jordan curve theorem a theorem. Cutting a curve
into two arcs is only useful because neither arc, alone, disconnects
anything.

## Statement

> [!theorem] An arc does not separate
> Let $A \subseteq \mathbb{C}$ be an [[def-arc|arc]]. Then $\mathbb{C} \setminus A$ is [[def-connected|connected]].

## Notes

> [!note]- Notes (click to expand)
> - The proof is by contradiction through [[thm-brouwer-fixed-point]] again: a bounded component of the complement, together with the fact that an arc is an absolute retract, produces a fixed-point-free self-map of a disc.
> - The corresponding statement for a [[def-jordan-curve|Jordan curve]] is false, and that is the content of [[thm-jordan-curve]].
