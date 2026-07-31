---
id: f8c2c5f4c1ad
status: proved
type: lemma
references:
  - "[[ref-beck|Beck et al., §4.1]]"
---

# Lemma — the standard parametrisation of a circle, its derivative and its length

Every computation below runs through this one parametrisation, and the two
facts it carries — the derivative and the length — are what turn a statement
about a circle into a statement about an integral over $[0, 2\pi]$.

## Statement

> [!lemma] Standard parametrisation of a circle
> Let $w \in \mathbb{C}$ and $r > 0$, and set $\gamma(t) = w + r e^{it}$ for $t \in [0, 2\pi]$ ([[def-complex-exponential|exponential]]). Then
> 1. $\gamma$ is a [[def-piecewise-smooth-path|simple closed smooth path]] whose image is the [[def-circle-and-disks|circle]] $C[w,r]$, traversed counter-clockwise;
> 2. $\gamma'(t) = i r e^{it}$;
> 3. $\operatorname{length}(C[w,r]) = 2\pi r$ ([[def-length-of-path|length]]).

## Proof

> [!note]- Proof (click to expand)
> **(1)** For every $t$, $|\gamma(t) - w| = r \, |e^{it}| = r$ by [[def-complex-exponential]], so the image lies in $C[w,r]$; conversely every $z$ with $|z-w| = r$ is $w + r e^{it}$ for exactly one $t \in [0, 2\pi)$, so $\gamma$ is onto $C[w,r]$ and injective on $[0, 2\pi)$. Also $\gamma(0) = \gamma(2\pi) = w + r$, so the path is closed. The argument of $\gamma(t) - w$ increases with $t$, which is the counter-clockwise orientation.
>
> **(2)** By [[lem-exponential-derivative]], $\gamma'(t) = r \frac{d}{dt} e^{it} = i r e^{it}$. This is continuous, and $|\gamma'(t)| = r > 0$, so $\gamma$ is smooth in the sense of [[def-piecewise-smooth-path]].
>
> **(3)** By [[def-length-of-path]] and (2),
> $$
> \operatorname{length}(C[w,r]) \; = \; \int_0^{2\pi} |i r e^{it}| \, dt \; = \; \int_0^{2\pi} r \, dt \; = \; 2\pi r . \qquad \square
> $$
