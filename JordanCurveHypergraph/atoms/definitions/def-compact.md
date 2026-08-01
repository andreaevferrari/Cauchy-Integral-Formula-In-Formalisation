---
id: 13c722ac7f98
type: definition
lean:
  - decl: IsCompact
    module: Mathlib.Topology.Defs.Filter
    line: 276
    state: proven
    rev: 905b95818eb3
references:
  - "[[ref-beck|Beck et al., §1.4]]"
---

# Definition — compact set

The property that turns a supremum into a maximum. Every use of it in this
network is that one use: a continuous real function on a compact set attains
its bound, so an estimate may be written with $\max$ rather than $\sup$.

## Statement

> [!definition] Compact
> A set $K \subseteq \mathbb{C}$ is *compact* if every cover of $K$ by [[def-open-set|open]] sets has a finite subcover, equivalently if $K$ is closed and bounded.
