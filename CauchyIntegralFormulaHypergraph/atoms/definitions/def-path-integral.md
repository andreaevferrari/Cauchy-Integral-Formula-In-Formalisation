---
id: 8d4e527ff597
type: definition
lean:
  - decl: circleIntegral
    module: Mathlib.MeasureTheory.Integral.CircleIntegral
    line: 385
    state: proven
    rev: 905b95818eb3
references:
  - "[[ref-beck|Beck et al., §4.1]]"
---

# Definition — the integral of a complex function along a path

The integral is pulled back to the interval by the parametrisation, so every
statement about it is in the end a statement about an integral of a
complex-valued function of a real variable. The value does not depend on
which parametrisation is chosen.

## Statement

> [!definition] Path integral
> Let $\gamma : [a,b] \to \mathbb{C}$ be a [[def-piecewise-smooth-path|piecewise smooth path]] and let $f$ be [[def-continuity|continuous]] on the image of $\gamma$. Then
> $$
> \int_\gamma f \; = \; \int_\gamma f(z) \, dz \; := \; \int_a^b f(\gamma(t)) \, \gamma'(t) \, dt ,
> $$
> the right-hand side being an [[def-integral-over-real-interval|integral over a real interval]].
