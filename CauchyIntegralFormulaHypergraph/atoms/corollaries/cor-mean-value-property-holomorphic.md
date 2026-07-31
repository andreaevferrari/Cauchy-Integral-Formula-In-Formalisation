---
id: 182d3a6aa611
status: proved
type: corollary
references:
  - "[[ref-beck|Beck et al., §4.4, Corollary 4.4.5]]"
---

# Corollary — the value at the centre is the average over the circle

The integral formula restated with the kernel parametrised away. In this
form the content is visible at a glance: no averaging, no weighting — the
value at the centre is the plain mean of the boundary values, and the same
holds separately for the real and imaginary parts.

## Statement

> [!corollary] Mean value property
> Let $f = u + iv$ be [[def-holomorphic|holomorphic]] on an [[def-open-set|open set]] containing the [[def-circle-and-disks|closed disk]] $\overline{D}[w,R]$, with $u, v$ real-valued. Then
> $$
> \begin{aligned}
> f(w) &= \frac{1}{2\pi} \int_0^{2\pi} f\big(w + R e^{it}\big) \, dt , \\
> u(w) &= \frac{1}{2\pi} \int_0^{2\pi} u\big(w + R e^{it}\big) \, dt , \\
> v(w) &= \frac{1}{2\pi} \int_0^{2\pi} v\big(w + R e^{it}\big) \, dt .
> \end{aligned}
> $$

## Proof

> [!note]- Proof (click to expand)
> By [[lem-circle-parametrisation]], $\gamma(t) = w + R e^{it}$, $0 \le t \le 2\pi$, parametrises $C[w,R]$ counter-clockwise with $\gamma'(t) = i R e^{it}$. Expanding [[thm-cauchy-integral-formula-circle]] by [[def-path-integral]],
> $$
> f(w) \; = \; \frac{1}{2\pi i} \int_0^{2\pi} \frac{f\big(w + R e^{it}\big)}{w + R e^{it} - w} \, i R e^{it} \, dt \; = \; \frac{1}{2\pi} \int_0^{2\pi} f\big(w + R e^{it}\big) \, dt ,
> $$
> the middle step cancelling $i R e^{it}$ against the denominator $R e^{it}$. Writing $f = u + iv$ and splitting the last integral into [[def-modulus-and-parts|real and imaginary parts]],
> $$
> u(w) + i \, v(w) \; = \; \frac{1}{2\pi} \int_0^{2\pi} u\big(w + R e^{it}\big) \, dt \; + \; i \, \frac{1}{2\pi} \int_0^{2\pi} v\big(w + R e^{it}\big) \, dt .
> $$
> Both integrals are real, so equating real and imaginary parts gives the two remaining identities. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The real and imaginary parts of a holomorphic function are harmonic, and the mean value property stated here for $u$ and $v$ is the defining property of harmonic functions. This is the shortest route from complex analysis to that fact.
