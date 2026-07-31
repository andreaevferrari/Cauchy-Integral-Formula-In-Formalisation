---
id: 841cf09b875a
status: proved
type: proposition
references:
  - "[[ref-beck|Beck et al., §4.4, Proposition 4.4.6]]"
---

# Proposition — a region contains the inside of a simple closed path exactly when the path is contractible in it

A statement about plane topology proved by complex analysis rather than the
other way round. It is what lets the integral formula be stated with the
hypothesis $\gamma \sim_G 0$, which is checkable, in place of "$G$ contains
the inside of $\gamma$", which is not.

## Statement

> [!proposition] Contractibility detects the interior
> Let $G$ be a [[def-region|region]] and let $\gamma$ be a simple closed [[def-piecewise-smooth-path|piecewise smooth path]] in $G$. Then $G$ contains the [[def-inside-of-path|inside]] of $\gamma$ if and only if $\gamma \sim_G 0$ ($G$-[[def-contractible-path|contractible]]).

## Proof

> [!note]- Proof (click to expand)
> **($\Rightarrow$)** Suppose $G$ contains the inside of $\gamma$, and let $\overline{D}[w,R]$ be any [[def-circle-and-disks|closed disk]] contained in that inside. By [[thm-annulus-homotopy]] there is a homotopy from $\gamma$ to $C[w,R]$ staying in the inside of $\gamma$ minus $\overline{D}[w,R]$, hence staying in $G$; and $C[w,R] \sim_G 0$, since the disk it bounds lies in $G$ and the radial contraction $h(t,s) = w + (1-s) R e^{2\pi i t}$ takes values there. By transitivity of $G$-[[def-homotopic-paths|homotopy]] ([[lem-homotopy-is-equivalence-relation]]), $\gamma \sim_G 0$.
>
> **($\Leftarrow$)** Suppose $\gamma \sim_G 0$ but $G$ does not contain the inside of $\gamma$. Pick $w$ inside $\gamma$ with $w \notin G$, and set $g(z) = \frac{1}{z-w}$, which is [[def-holomorphic|holomorphic]] on $G$ because $w \notin G$. Since $\gamma \sim_G 0$, [[cor-integral-zero-contractible-path]] gives
> $$
> \int_\gamma g(z) \, dz \; = \; 0 .
> $$
> On the other hand, choose $R > 0$ with $\overline{D}[w,R]$ inside $\gamma$. By [[thm-annulus-homotopy]] there is a homotopy from $\gamma$ to $C[w,R]$ avoiding $\overline{D}[w,R]$, so in particular a homotopy in $\mathbb{C} \setminus \{w\}$, where $g$ is holomorphic. By [[thm-cauchy]] and [[lem-circle-integral-inverse]],
> $$
> \int_\gamma g(z) \, dz \; = \; \int_{C[w,R]} \frac{dz}{z-w} \; = \; 2\pi i .
> $$
> Since $2\pi i \neq 0$, this is a contradiction, and $G$ must contain the inside of $\gamma$. $\square$

## Notes

> [!note]- Notes (click to expand)
> - The direction that does the work is ($\Leftarrow$), and it is where a holomorphic function is used to prove something purely topological: the function $\frac{1}{z-w}$ detects a puncture that no argument about connectedness was going to see.
