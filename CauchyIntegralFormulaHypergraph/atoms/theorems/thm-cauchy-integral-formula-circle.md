---
id: 4699c8ce3408
status: proved
type: theorem
lean:
  - decl: Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
    module: Mathlib.Analysis.Complex.CauchyIntegral
    line: 428
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §4.4, Theorem 4.4.4]]"
---

# Theorem — a holomorphic function is recovered from its values on a circle

The value at the centre is determined by the values on the boundary. Nothing
in real calculus behaves this way: a smooth real function on a disk may be
changed at the centre without disturbing the boundary at all.

## Statement

> [!theorem] Cauchy's integral formula for a circle
> Let $f$ be [[def-holomorphic|holomorphic]] on an [[def-open-set|open set]] containing the [[def-circle-and-disks|closed disk]] $\overline{D}[w,R]$. Then
> $$
> f(w) \; = \; \frac{1}{2\pi i} \int_{C[w,R]} \frac{f(z)}{z - w} \, dz .
> $$

## Proof

> [!note]- Proof (click to expand)
> Let $G$ be an [[def-open-set|open set]] containing $\overline{D}[w,R]$ on which $f$ is [[def-holomorphic|holomorphic]], and put $H := G \setminus \{w\}$. The function $z \mapsto \frac{f(z)}{z-w}$ is holomorphic on $H$.
>
> **Step 1: every [[def-circle-and-disks|circle]] about $w$ gives the same integral.** For $0 < r < R$ the map
> $$
> h(t,s) \; = \; w + \big( (1-s) r + s R \big) e^{2\pi i t}, \qquad (t,s) \in [0,1]^2 ,
> $$
> is continuous, takes values in $H$ because its radius $(1-s)r + sR$ stays in $[r,R]$ and is therefore never $0$, and satisfies the three conditions of [[def-homotopic-paths]]. Hence $C[w,r] \sim_H C[w,R]$, and [[thm-cauchy]] gives
> $$
> \int_{C[w,R]} \frac{f(z)}{z-w} \, dz \; = \; \int_{C[w,r]} \frac{f(z)}{z-w} \, dz .
> $$
>
> **Step 2: the error is controlled by the oscillation of $f$.** By [[lem-circle-integral-inverse]], $\int_{C[w,r]} \frac{dz}{z-w} = 2\pi i$, so $2\pi i \, f(w) = f(w) \int_{C[w,r]} \frac{dz}{z-w}$. Combining this with Step 1,
> $$
> \left| \int_{C[w,R]} \frac{f(z)}{z-w} \, dz - 2\pi i \, f(w) \right| \; = \; \left| \int_{C[w,r]} \frac{f(z) - f(w)}{z - w} \, dz \right| .
> $$
> By [[prop-integral-length-bound]], and since $|z - w| = r$ on $C[w,r]$ while $\operatorname{length}(C[w,r]) = 2\pi r$ by [[lem-circle-parametrisation]], this is at most
> $$
> \max_{z \in C[w,r]} \frac{|f(z) - f(w)|}{r} \cdot 2\pi r \; = \; 2\pi \max_{z \in C[w,r]} |f(z) - f(w)| .
> $$
>
> **Step 3: shrink the circle.** Let $\varepsilon > 0$. Since $f$ is holomorphic on $G$ it is continuous at $w$, so there is $\delta > 0$ with $|f(z) - f(w)| < \frac{\varepsilon}{2\pi}$ whenever $|z - w| < \delta$. Taking $r = \frac{\delta}{2}$, which is admissible once $\delta < 2R$, every $z \in C[w,r]$ satisfies $|z-w| < \delta$, and Step 2 gives
> $$
> \left| \int_{C[w,R]} \frac{f(z)}{z-w} \, dz - 2\pi i \, f(w) \right| \; < \; \varepsilon .
> $$
> The left-hand side does not depend on $\varepsilon$, and $\varepsilon > 0$ was arbitrary, so it is $0$. Dividing by $2\pi i$ gives the formula. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The mechanism is worth separating from the computation: Step 1 says the integral is the same on every circle about $w$, so it may be evaluated in the limit of small circles, where $f$ is nearly constant and [[lem-circle-integral-inverse]] applies. Holomorphy enters only through [[thm-cauchy]] in Step 1 — Steps 2 and 3 use nothing beyond continuity.
> - The right-hand side involves only the values of $f$ on $C[w,R]$. So those values determine $f(w)$, and iterating the observation over all interior points gives the rigidity that the rest of the subject is built from.
