---
type: notation
---

# Notation

Every symbol this network uses, with the card that defines it. The table is
normative: one name and one symbol per concept, registered here when the card
is written. A row whose Card column is `—` is a declared primitive, not a
debt: something this network takes from real analysis and does not define.

## The cast — role letters

Recurring roles have fixed letters, pool-wide. Writing a source's statement
into a card translates its lettering into this cast, exactly as it translates
its terminology.

| Letter | Role |
|---|---|
| $G$ | the region a function is holomorphic on — the ambient set of every hypothesis |
| $\Omega$ | an open set with no connectedness assumed |
| $H$, $A$ | sets built from $G$ by removing something: the punctured $G \setminus \{w\}$, the annulus between two paths |
| $f$ | the holomorphic function under study; $u, v$ its real and imaginary parts |
| $g$ | an auxiliary function introduced inside a proof |
| $\gamma$ | a path; $\gamma_0, \gamma_1$ the two ends of a homotopy; $\sigma$ a constant path |
| $z$ | the variable of integration, running along $\gamma$ |
| $w$ | the point the value is recovered at — always inside the contour, never on it |
| $r$, $R$ | radii, with $r < R$ when both occur: $r$ shrinks, $R$ is given |
| $t$, $s$ | the parameters of a path and of a homotopy respectively |
| $\varepsilon$, $\delta$ | the two halves of a continuity argument |
| $\theta$ | an argument (angle) of a complex number |

## The table — notation with its defining card

| Notation | Meaning | Card |
|---|---|---|
| $C[a,r]$ | the circle of centre $a$ and radius $r$, counter-clockwise unless said otherwise | [[def-circle-and-disks]] |
| $D[a,r]$ | the open disk | [[def-circle-and-disks]] |
| $\overline{D}[a,r]$ | the closed disk | [[def-circle-and-disks]] |
| region | a non-empty open connected subset of $\mathbb{C}$ | [[def-region]] |
| holomorphic | complex-differentiable at every point of an open set | [[def-holomorphic]] |
| $f'$ | the complex derivative | [[def-holomorphic]] |
| $\int_\gamma f$ | the integral along a path, $\int_a^b f(\gamma(t)) \gamma'(t) \, dt$ | [[def-path-integral]] |
| $\operatorname{length}$ | the length of a path, $\int_a^b \lvert \gamma'(t) \rvert \, dt$ | [[def-length-of-path]] |
| $\gamma(t) = w + r e^{it}$ | the standard counter-clockwise parametrisation of $C[w,r]$ | [[lem-circle-parametrisation]] |
| $\exp$, $e^{z}$, $\pi$ | the exponential series, and $2\pi$ as the period of $t \mapsto e^{it}$ | [[def-complex-exponential]] |
| $\sim_G$ | $G$-homotopic: a continuous square of closed paths joining the two | [[def-homotopic-paths]] |
| $\sim_G 0$ | $G$-contractible: homotopic in $G$ to a constant path | [[def-contractible-path]] |
| inside | the bounded component of the complement of a simple closed path | [[def-inside-of-path]] |
| positively oriented | traversed with the inside on the left | [[def-positively-oriented-path]] |
| $\frac{f(z)}{z-w}$ | the Cauchy kernel against $f$ — the integrand of every statement here | [[thm-cauchy-integral-formula]] |

## The floor

Nothing complex is a primitive here: every notion in the table above has a
card, down to $\mathbb{C}$ itself. What this network does not define is the
mathematics that is not its subject — the real numbers, sets and functions,
and the analysis of one real variable.

A **fact** about anything on the floor still gets a card, however small,
which is why $\lvert \int_a^b g \rvert \le \int_a^b \lvert g \rvert$ is
[[lem-modulus-of-integral]] rather than an entry here, and why
$\frac{d}{dt} e^{it} = i e^{it}$ is [[lem-exponential-derivative]].

| Taken from | Used for |
|---|---|
| $\mathbb{R}$, its order and completeness | the coordinates of $\mathbb{C}$, and every $\varepsilon$–$\delta$ argument |
| sets, functions, finiteness | throughout |
| the Riemann integral of a continuous real function, its linearity and monotonicity | the real and imaginary halves of [[def-integral-over-real-interval]] |
| differentiation of a real variable, and term-by-term differentiation of a power series | [[lem-exponential-derivative]] |
| $\equiv$, identically equal | notation |

## Typography

Not mathematics, and not ground notions either — marks that structure a
proof.

| Mark | Use |
|---|---|
| $\Rightarrow$, $\Leftarrow$ | the two directions of an equivalence, as proof headings |
| $\square$ | end of proof |
