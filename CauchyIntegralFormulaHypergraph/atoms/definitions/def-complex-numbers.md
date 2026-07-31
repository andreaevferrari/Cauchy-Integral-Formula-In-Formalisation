---
id: 161ced703698
type: definition
lean:
  - decl: Complex
    module: Mathlib.Data.Complex.Basic
    line: 34
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §1.1]]"
---

# Definition — the complex numbers

Two descriptions of one object, and both are used throughout: an algebraic
one, in which $\mathbb{C}$ is a field where $-1$ has a square root, and a
geometric one, in which it is the plane. Every statement here reads the same
symbol both ways.

## Statement

> [!definition] The complex numbers
> $\mathbb{C}$ is the set $\mathbb{R}^2$ equipped with the addition of $\mathbb{R}^2$ and the multiplication
> $$
> (x_1, y_1) \cdot (x_2, y_2) \; = \; (x_1 x_2 - y_1 y_2, \; x_1 y_2 + x_2 y_1) .
> $$
> Writing $i = (0,1)$ and identifying $x \in \mathbb{R}$ with $(x,0)$, every element is uniquely $z = x + iy$ with $x, y \in \mathbb{R}$, and $i^2 = -1$. With these operations $\mathbb{C}$ is a field, and as a set it is the plane.
