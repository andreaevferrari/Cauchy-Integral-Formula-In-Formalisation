---
id: cd59e975f01c
status: proved
type: lemma
references:
  - "[[ref-beck|Beck et al., Exercise 4.5.4]]"
---

# Lemma — the integral of 1/(z−w) over a circle centred at w is 2πi

The one integral in the subject that is computed rather than deduced.
Everything below is, in the end, a comparison against it: the value $2\pi i$
in the integral formula is this value, and the factor $\frac{1}{2\pi i}$ is there to cancel it.

## Statement

> [!lemma] Circle integral of the Cauchy kernel
> For $w \in \mathbb{C}$ and $r > 0$, with $C[w,r]$ the [[def-circle-and-disks|circle]] oriented counter-clockwise,
> $$
> \int_{C[w,r]} \frac{dz}{z - w} \; = \; 2 \pi i .
> $$

## Proof

> [!note]- Proof (click to expand)
> By [[lem-circle-parametrisation]], $\gamma(t) = w + r e^{it}$, $0 \le t \le 2\pi$, parametrises $C[w,r]$ counter-clockwise with $\gamma'(t) = i r e^{it}$. By [[def-path-integral]],
> $$
> \int_{C[w,r]} \frac{dz}{z-w} \; = \; \int_0^{2\pi} \frac{i r e^{it}}{w + r e^{it} - w} \, dt \; = \; \int_0^{2\pi} \frac{i r e^{it}}{r e^{it}} \, dt \; = \; \int_0^{2\pi} i \, dt \; = \; 2 \pi i . \qquad \square
> $$

## Notes

> [!note]- Notes (click to expand)
> - The value does not depend on $r$, and that is the whole content: the integrand's singularity at $w$ is felt equally by every circle around it. Shrinking the circle is therefore free, which is what the argument for [[thm-cauchy-integral-formula-circle]] exploits.
