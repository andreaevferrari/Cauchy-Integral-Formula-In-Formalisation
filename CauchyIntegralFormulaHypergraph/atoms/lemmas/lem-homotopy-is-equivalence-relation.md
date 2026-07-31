---
id: b5747f4a38c1
status: proved
type: lemma
references:
  - "[[ref-beck|Beck et al., Exercises 4.5.14 and 4.5.15]]"
---

# Lemma — G-homotopy is an equivalence relation

Without this, "$\gamma_0 \sim_G \gamma_1$" would be a relation between an
ordered pair rather than a way of grouping paths, and no argument could chain
two deformations together.

## Statement

> [!lemma] Equivalence relation
> Let $G \subseteq \mathbb{C}$. Then $G$-[[def-homotopic-paths|homotopy]] is an equivalence relation on the set of closed paths in $G$: it is reflexive, symmetric and transitive.

## Proof

> [!note]- Proof (click to expand)
> **Reflexive.** For a closed path $\gamma$ in $G$, the map $h(t,s) = \gamma(t)$ is continuous into $G$ and satisfies the three conditions of [[def-homotopic-paths]], so $\gamma \sim_G \gamma$.
>
> **Symmetric.** If $h$ is a homotopy from $\gamma_0$ to $\gamma_1$, then $h'(t,s) = h(t, 1-s)$ is continuous into $G$, has $h'(t,0) = \gamma_1(t)$, $h'(t,1) = \gamma_0(t)$ and $h'(0,s) = h'(1,s)$, so $\gamma_1 \sim_G \gamma_0$.
>
> **Transitive.** Let $h_1$ be a homotopy from $\gamma_0$ to $\gamma_1$ and $h_2$ one from $\gamma_1$ to $\gamma_2$. Define
> $$
> h(t,s) \; = \; \begin{cases} h_1(t, 2s) & 0 \le s \le \tfrac{1}{2}, \\ h_2(t, 2s-1) & \tfrac{1}{2} \le s \le 1. \end{cases}
> $$
> The two formulas agree at $s = \tfrac{1}{2}$, where both give $\gamma_1(t)$, so $h$ is well defined and continuous on $[0,1]^2$, with values in $G$. It satisfies $h(t,0) = \gamma_0(t)$, $h(t,1) = \gamma_2(t)$, and $h(0,s) = h(1,s)$ because each of $h_1, h_2$ does. Hence $\gamma_0 \sim_G \gamma_2$. $\square$
