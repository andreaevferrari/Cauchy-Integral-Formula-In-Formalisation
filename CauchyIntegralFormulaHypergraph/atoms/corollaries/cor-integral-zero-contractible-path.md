---
id: 61a78354ffa8
status: proved
type: corollary
references:
  - "[[ref-beck|Beck et al., §4.3, Corollary 4.3.8]]"
---

# Corollary — a holomorphic function integrates to zero over a contractible path

The form of Cauchy's theorem that is actually applied: one path instead of
two, and a conclusion that is a number rather than an equality of integrals.

## Statement

> [!corollary] Vanishing over a contractible path
> Let $G \subseteq \mathbb{C}$ be a [[def-region|region]], let $f$ be [[def-holomorphic|holomorphic]] on $G$, and let $\gamma$ be a [[def-piecewise-smooth-path|piecewise smooth]] closed path with $\gamma \sim_G 0$ ($G$-[[def-contractible-path|contractible]]). Then
> $$
> \int_\gamma f \; = \; 0 .
> $$

## Proof

> [!note]- Proof (click to expand)
> By [[def-contractible-path]], $\gamma$ is $G$-[[def-homotopic-paths|homotopic]] to a constant path $\sigma$. By [[thm-cauchy]], $\int_\gamma f = \int_\sigma f$. A constant path has $\sigma' \equiv 0$, so by [[def-path-integral]] its integral is $\int_a^b f(\sigma(t)) \cdot 0 \, dt = 0$. $\square$
