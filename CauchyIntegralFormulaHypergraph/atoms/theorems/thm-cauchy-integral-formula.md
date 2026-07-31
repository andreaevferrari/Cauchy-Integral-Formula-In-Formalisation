---
id: 71fa1b1bb941
status: proved
type: theorem
lean:
  - decl: Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    module: Mathlib.Analysis.Complex.CauchyIntegral
    line: 532
    state: proven
    rev: 905b95818eb3
references:
  - "[[ref-beck|Beck et al., §4.4, Theorem 4.4.7]]"
---

# Theorem — a holomorphic function is recovered from its values on any enclosing path

The root of this network. The circle in the special case is replaced by an
arbitrary enclosing contour, and the value of $f$ at an interior point is
still read off the boundary values alone.

## Statement

> [!theorem] Cauchy's integral formula
> Let $f$ be [[def-holomorphic|holomorphic]] on a [[def-region|region]] $G$, and let $\gamma$ be a [[def-positively-oriented-path|positively oriented]] simple closed [[def-piecewise-smooth-path|piecewise smooth]] path with $w$ [[def-inside-of-path|inside]] $\gamma$ and $\gamma \sim_G 0$ ($G$-[[def-contractible-path|contractible]]). Then
> $$
> f(w) \; = \; \frac{1}{2\pi i} \int_\gamma \frac{f(z)}{z - w} \, dz .
> $$

## Proof

> [!note]- Proof (click to expand)
> Since $\gamma \sim_G 0$, [[prop-interior-in-region-iff-contractible]] gives that $G$ contains the inside of $\gamma$. In particular $w \in G$, and $G$ being open there is $R > 0$ with $\overline{D}[w,R] \subseteq G$ and $\overline{D}[w,R]$ inside $\gamma$.
>
> Put $H := G \setminus \{w\}$, on which $z \mapsto \frac{f(z)}{z-w}$ is [[def-holomorphic|holomorphic]]. Let $A$ be the inside of $\gamma$ with $\overline{D}[w,R]$ removed; then $A \subseteq H$, because $A \subseteq G$ by the previous paragraph and $w \notin A$. By [[thm-annulus-homotopy]], $\gamma \sim_A C[w,R]$, hence $\gamma \sim_H C[w,R]$. Applying [[thm-cauchy]] on $H$,
> $$
> \int_\gamma \frac{f(z)}{z-w} \, dz \; = \; \int_{C[w,R]} \frac{f(z)}{z-w} \, dz .
> $$
> The right-hand side is $2\pi i \, f(w)$ by [[thm-cauchy-integral-formula-circle]], whose hypothesis holds because $\overline{D}[w,R] \subseteq G$ and $f$ is holomorphic on $G$. Dividing by $2\pi i$ gives the formula. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The hypothesis $\gamma \sim_G 0$ replaces the more obvious "$G$ contains the inside of $\gamma$". The two are equivalent by [[prop-interior-in-region-iff-contractible]], and the contractibility form is the one that survives into later statements where the path is no longer simple.
> - Both topological inputs of the argument, [[thm-jordan-curve]] and [[thm-annulus-homotopy]], are unproved debts, as is [[thm-cauchy]] itself. What this card establishes is the reduction of the general formula to the circle case, and that reduction is complete.
