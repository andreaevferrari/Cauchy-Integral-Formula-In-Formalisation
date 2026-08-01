---
label: LeanEval
type: reference
---

# [LeanEval] The lean-eval benchmark, problem `jordan_curve`

**Lean AI formalization leaderboard**, problem `jordan_curve`.
<https://lean-lang.org/eval/problems/jordan_curve/>

Where this library's development started. The benchmark poses the statement

$$
\operatorname{card}\big(\pi_0(\mathbb{C} \setminus r(S^1))\big) = 2
$$

for a continuous injective $r$, and records the solutions submitted against
it. The problem was contributed by Kim Morrison, citing §48 of
[[ref-knill|Knill's survey]]; its notes observe that Mathlib has
`Metric.sphere`, `EuclideanSpace`, `ConnectedComponents` and `Nat.card` but
no Jordan curve theorem and no winding numbers, so the statement needs no new
definitions and nothing in the library discharges it. One of those, `rkirov/jordan_pick` (Apache 2.0), is what this
repository's Lean development grew from; `JordanCurve/PROVENANCE.md` records
the commit and everything changed since.

The theorem was formalized in Mizar (Korniłowicz et al., 2005) and in HOL
Light (Hales, 2007), and in neither Lean nor the Coq/Rocq standard libraries
before this benchmark. Its history is [[ref-jordan|Jordan's statement of
1887]] and [[ref-veblen|Veblen's proof of 1905]]; the argument formalized
here is [[ref-maehara|Maehara's of 1984]], chosen for economy rather than
priority.

The benchmark statement gives only the count of two components. The cards
here need more — which component is bounded, and that the curve is the
boundary of each — and those are proved in the development rather than taken
from the benchmark.

```bibtex
@misc{leaneval,
  author = {{Lean AI formalization leaderboard}},
  title  = {lean-eval benchmark, problem \texttt{jordan\_curve}},
  url    = {https://lean-lang.org/eval/problems/jordan_curve/},
  year   = {2026},
}
```
