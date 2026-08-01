---
id: a11eadf5f31b
type: definition
references:
  - "[[ref-beck|Beck et al., §2.1]]"
---

# Definition — the limit of a complex function at a point

The definition is the real one with the absolute value read as the
[[def-modulus-and-parts|modulus]]. What changes is not the definition but
its force: $h \to 0$ now approaches from every direction of the plane at
once.

## Statement

> [!definition] Limit
> Let $\Omega \subseteq \mathbb{C}$, let $f : \Omega \to \mathbb{C}$, and let $z_0$ be a point with $\Omega$ containing points arbitrarily close to it. Then $\lim_{z \to z_0} f(z) = L$ means: for every $\varepsilon > 0$ there is $\delta > 0$ such that every $z \in \Omega$ with $0 < |z - z_0| < \delta$ satisfies $|f(z) - L| < \varepsilon$.
