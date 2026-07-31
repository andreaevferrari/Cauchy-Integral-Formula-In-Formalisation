---
id: 5da5d2799a15
status: proved
type: proposition
references:
  - "[[ref-beck|Beck et al., §4.1, Proposition 4.1.1(d)]]"
---

# Proposition — an integral is bounded by the maximum of the integrand times the length

The only estimate the argument for the integral formula needs. It converts a
bound on the integrand, which continuity supplies, into a bound on the
integral, which is what has to be made small.

## Statement

> [!proposition] Estimate for a path integral
> Let $\gamma$ be a [[def-piecewise-smooth-path|piecewise smooth path]] and let $f$ be [[def-continuity|continuous]] on its image. Then
> $$
> \left| \int_\gamma f \right| \; \le \; \max_{z \in \gamma} |f(z)| \cdot \operatorname{length}(\gamma) .
> $$

## Proof

> [!note]- Proof (click to expand)
> Parametrise $\gamma$ on $[a,b]$. By [[def-path-integral]] and [[lem-modulus-of-integral]],
> $$
> \left| \int_\gamma f \right| \; = \; \left| \int_a^b f(\gamma(t)) \gamma'(t) \, dt \right| \; \le \; \int_a^b |f(\gamma(t))| \, |\gamma'(t)| \, dt .
> $$
> Bounding $|f(\gamma(t))|$ by its maximum over the image of $\gamma$, which is attained since the image is [[def-compact|compact]] and $f$ is continuous, and using [[def-length-of-path]],
> $$
> \int_a^b |f(\gamma(t))| \, |\gamma'(t)| \, dt \; \le \; \max_{z \in \gamma} |f(z)| \int_a^b |\gamma'(t)| \, dt \; = \; \max_{z \in \gamma} |f(z)| \cdot \operatorname{length}(\gamma) . \qquad \square
> $$

