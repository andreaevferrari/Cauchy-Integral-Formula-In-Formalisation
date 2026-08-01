---
id: 601adc77e47c
status: formal
type: theorem
lean:
  - decl: JordanCurve.bounded_component_unique
    module: JordanCurve.Component.Unbounded
    line: 467
    state: proven
references:
  - "Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, 1984"
---

# Theorem — the bounded component is unique

Maehara's Step B. With [[thm-exists-bounded-component]] and
[[thm-unique-unbounded-component]] this is the last of the three facts the
count of two is assembled from.

## Statement

> [!theorem] The bounded component is unique
> Let $J$ be a [[def-jordan-curve|Jordan curve]]. Any two bounded [[def-connected|connected components]] of $\mathbb{C} \setminus J$ coincide.

## Notes

> [!note]- Notes (click to expand)
> - Every bounded component is shown to contain the midpoint $z_0$ of [[def-maehara-configuration]], which forces them all to be the same one.
> - The argument is again by exhibiting a bottom-to-top path in the rectangle that misses one of the two arcs, and appealing to [[thm-crossing-lemma]].
