---
id: dd2b28efcf02
type: definition
lean:
  - decl: IsOpen
    module: Mathlib.Topology.Defs.Basic
    line: 95
    state: proven
    rev: 905b95818eb3
references:
  - "[[ref-beck|Beck et al., §1.4]]"
---

# Definition — open set

## Statement

> [!definition] Open
> A set $\Omega \subseteq \mathbb{C}$ is *open* if for every $z \in \Omega$ there is $r > 0$ with $D[z,r] \subseteq \Omega$, where $D[z,r]$ is the [[def-circle-and-disks|open disk]]. A set is *closed* if its complement is open.
