---
id: c0102040b7fd
type: definition
lean:
  - decl: Path.Homotopic
    module: Mathlib.Topology.Homotopy.Path
    line: 241
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §4.3]]"
---

# Definition — G-homotopic closed paths

Two closed paths are the same for the purposes of integration when one can
be deformed into the other without leaving the set where the integrand is
defined. The deformation is a continuous square-worth of paths, every one of
them closed.

## Statement

> [!definition] $G$-homotopic
> Let $G \subseteq \mathbb{C}$ and let $\gamma_0, \gamma_1 : [0,1] \to G$ be closed paths. Then $\gamma_0$ is *$G$-homotopic* to $\gamma_1$ if there is a [[def-continuity|continuous]] $h : [0,1]^2 \to G$ with
> $$
> h(t,0) = \gamma_0(t), \qquad h(t,1) = \gamma_1(t), \qquad h(0,s) = h(1,s)
> $$
> for all $s, t \in [0,1]$. Such an $h$ is a *homotopy*, and the relation is written $\gamma_0 \sim_G \gamma_1$.

## Notes

> [!note]- Notes (click to expand)
> - The third condition is what keeps every intermediate path $h(\cdot, s)$ closed; without it the deformation could open the loop up.
> - That $\sim_G$ is an equivalence relation is [[lem-homotopy-is-equivalence-relation]]. It is also invariant under reparametrisation, so it descends from parametrised paths to curves.
