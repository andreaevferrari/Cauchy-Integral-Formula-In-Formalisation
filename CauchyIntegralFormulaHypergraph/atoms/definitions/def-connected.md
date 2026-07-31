---
id: d83e89332774
type: definition
lean:
  - decl: IsConnected
    module: Mathlib.Topology.Connected.Basic
    line: 55
    state: proven
    rev: fabf563a7c95
references:
  - "[[ref-beck|Beck et al., §1.4]]"
---

# Definition — connected set, and its connected components

## Statement

> [!definition] Connected
> A set $X \subseteq \mathbb{C}$ is *connected* if it cannot be written as the union of two disjoint non-empty sets, each [[def-open-set|open]] in $X$. A *connected component* of $X$ is a maximal connected subset of $X$.
