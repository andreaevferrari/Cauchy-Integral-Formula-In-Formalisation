---
id: 23a431eb2a6c
type: definition
lean:
  - decl: intervalIntegral
    module: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
    line: 657
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §4.1]]"
---

# Definition — the integral of a complex-valued function over a real interval

The bottom of the tower. Every integral in this network is reduced to this
one by a parametrisation, and this one is reduced to two real integrals by
taking parts — so nothing below it is complex analysis.

## Statement

> [!definition] Integral over a real interval
> Let $g : [a,b] \to \mathbb{C}$ be [[def-continuity|continuous]]. Then
> $$
> \int_a^b g(t) \, dt \; = \; \int_a^b \operatorname{Re}\, g(t) \, dt \; + \; i \int_a^b \operatorname{Im}\, g(t) \, dt ,
> $$
> the two integrals on the right being Riemann integrals of continuous real functions ([[def-modulus-and-parts|real and imaginary parts]]). The integral is $\mathbb{C}$-linear in $g$.
