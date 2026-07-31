---
id: 7054378fb3d1
type: theorem
status: debt
references:
  - "[[ref-beck|Beck et al., §4.4 — assumed, not proved]]"
---

# Theorem — a positively oriented path is homotopic to an interior circle in the annulus between them

Assumed here, not proved. This is the deformation that transports the circle
case of the integral formula out to an arbitrary path.

## Statement

> [!theorem] Annulus homotopy
> Let $\gamma$ be a [[def-positively-oriented-path|positively oriented]] [[def-piecewise-smooth-path|piecewise smooth]] simple closed path and let $\overline{D}[w,R]$ be a [[def-circle-and-disks|closed disk]] contained in the [[def-inside-of-path|inside]] of $\gamma$. Let $A$ be the [[def-region|region]] between $\gamma$ and $C[w,R]$, that is, the inside of $\gamma$ with $\overline{D}[w,R]$ removed. Then $\gamma \sim_A C[w,R]$, the [[def-homotopic-paths|homotopy]] being taken with the counter-clockwise orientation on $C[w,R]$.

## Notes

> [!note]- Notes (click to expand)
> - Carried as a debt on purpose, on the same footing as [[thm-jordan-curve]]: the source assumes it and offers no argument.
> - The point of insisting the homotopy stays in $A$ is that the integrand $\frac{f(z)}{z-w}$ is only holomorphic away from $w$, so a deformation sweeping across $w$ would be worthless.
