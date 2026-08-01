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
it. One of those, `rkirov/jordan_pick` (Apache 2.0), is what this
repository's Lean development grew from; `JordanCurve/PROVENANCE.md` records
the commit and everything changed since.

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
