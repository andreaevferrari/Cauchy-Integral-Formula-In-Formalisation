---
id: c680ed9d2016
type: definition
lean:
  - decl: DifferentiableOn
    module: Mathlib.Analysis.Calculus.FDeriv.Defs
    line: 163
    state: proven
    rev: 905b95818eb3
references:
  - "[[ref-beck|Beck et al., §2.2]]"
---

# Definition — holomorphic function

Complex differentiability at a point asks for a limit that exists no matter
which direction $h$ approaches $0$ from — in the plane that is infinitely
many directions at once, and the resulting rigidity is what separates this
subject from real calculus.

## Statement

> [!definition] Holomorphic function
> Let $\Omega \subseteq \mathbb{C}$ be [[def-open-set|open]]. A function $f : \Omega \to \mathbb{C}$ is *holomorphic* on $\Omega$ if for every $z_0 \in \Omega$ the [[def-limit-in-c|limit]]
> $$
> f'(z_0) \; = \; \lim_{h \to 0} \frac{f(z_0 + h) - f(z_0)}{h}, \qquad h \in \mathbb{C} \setminus \{0\},
> $$
> exists. A function holomorphic on all of $\mathbb{C}$ is *entire*.
