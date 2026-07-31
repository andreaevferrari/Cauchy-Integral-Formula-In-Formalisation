---
id: 5c2d3daeaca0
type: definition
lean:
  - decl: Complex.exp
    module: Mathlib.Analysis.Complex.Exponential
    line: 62
    state: proven
    rev: fabf563a7c95
  - decl: Real.pi
    module: Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
    line: 127
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §3.4]]"
---

# Definition — the complex exponential and the constant pi

Defined by its series, not by anything geometric. That the circle and the
number $\pi$ come out of a power series, rather than being put in by hand, is
what makes every parametrisation below a computation instead of a picture.

## Statement

> [!definition] Exponential and $\pi$
> For $z \in \mathbb{C}$ ([[def-complex-numbers|complex number]]),
> $$
> \exp(z) \; = \; e^{z} \; = \; \sum_{k \ge 0} \frac{z^k}{k!} ,
> $$
> the series converging absolutely for every $z$. The function $t \mapsto e^{it}$ on $\mathbb{R}$ takes values of [[def-modulus-and-parts|modulus]] $1$, is periodic, and $2\pi$ denotes its smallest positive period; $t \mapsto e^{it}$ maps $[0, 2\pi)$ bijectively onto $\{ z : |z| = 1 \}$.
