---
id: 5a6cf400257d
status: formal
type: theorem
lean:
  - decl: JordanCurve.Brouwer.no_retraction
    module: JordanCurve.Brouwer
    line: 153
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Theorem — the disc does not retract onto its boundary circle

The geometric content behind Brouwer. A retraction would let the boundary
circle be contracted inside itself, and the once-around loop cannot be
contracted.

## Statement

> [!theorem] No retraction
> There is no [[def-continuity|continuous]] map $\rho$ from the closed unit [[def-circle-and-disks|disk]] onto its boundary circle with $\rho(z) = z$ for every $z$ on that circle.

## Notes

> [!note]- Notes (click to expand)
> - The formal proof lifts the once-around loop through the covering $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$: a nullhomotopy would force the lift to return to its starting value, and it returns one turn away.
