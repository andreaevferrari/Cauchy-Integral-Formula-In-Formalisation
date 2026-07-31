---
id: 0baf0e4b6d60
type: definition
lean:
  - decl: Complex.normSq
    module: Mathlib.Data.Complex.Basic
    line: 509
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §1.2]]"
---

# Definition — real part, imaginary part, conjugate and modulus

The four ways of taking a complex number apart. The modulus is the Euclidean
distance of the plane, which is what lets every estimate in this network be
an estimate about distances.

## Statement

> [!definition] Parts, conjugate, modulus
> For $z = x + iy \in \mathbb{C}$ with $x, y \in \mathbb{R}$ ([[def-complex-numbers|complex number]]), the *real part* is $\operatorname{Re}(z) = x$, the *imaginary part* is $\operatorname{Im}(z) = y$, the *conjugate* is $\overline{z} = x - iy$, and the *modulus* is
> $$
> |z| \; = \; \sqrt{x^2 + y^2} \; = \; \sqrt{z \overline{z}} .
> $$
> The modulus is multiplicative, satisfies the triangle inequality, and $\operatorname{Re}(z) \le |z|$; the map $(z_1, z_2) \mapsto |z_1 - z_2|$ is the Euclidean metric of the plane.
