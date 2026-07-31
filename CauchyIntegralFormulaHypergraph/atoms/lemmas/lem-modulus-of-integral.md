---
id: 6c23268772e2
status: proved
type: lemma
lean:
  - decl: intervalIntegral.norm_integral_le_integral_norm
    module: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
    line: 746
    state: proven
    rev: 905b95818eb3
references:
  - "Standard real analysis"
---

# Lemma — the modulus of an integral is at most the integral of the modulus

The triangle inequality, in the limit. For a real integrand it is immediate
from monotonicity; for a complex one the two sides are no longer comparable
term by term, and the rotation that repairs this is the whole content.

## Statement

> [!lemma] Modulus of an integral
> Let $g : [a,b] \to \mathbb{C}$ be [[def-continuity|continuous]], and let $\int_a^b$ be the [[def-integral-over-real-interval|integral over a real interval]]. Then
> $$
> \left| \int_a^b g(t) \, dt \right| \; \le \; \int_a^b |g(t)| \, dt .
> $$

## Proof

> [!note]- Proof (click to expand)
> Write $I = \int_a^b g(t) \, dt$. If $I = 0$ the inequality is immediate, since the right-hand side is non-negative. Otherwise write $I = |I| e^{i\theta}$ with $\theta \in \mathbb{R}$ ([[def-complex-exponential]]), so that
> $$
> |I| \; = \; e^{-i\theta} I \; = \; \int_a^b e^{-i\theta} g(t) \, dt .
> $$
> The left-hand side is real, so the right-hand side equals its own real part:
> $$
> |I| \; = \; \int_a^b \operatorname{Re}\big( e^{-i\theta} g(t) \big) \, dt .
> $$
> For any $z \in \mathbb{C}$ one has $\operatorname{Re}(z) \le |z|$ ([[def-modulus-and-parts]]), so the integrand is bounded by $|e^{-i\theta} g(t)| = |g(t)|$, and monotonicity of the integral of real functions gives
> $$
> |I| \; \le \; \int_a^b |g(t)| \, dt . \qquad \square
> $$
