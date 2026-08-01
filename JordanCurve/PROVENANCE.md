# Provenance

## What this library is

Maehara's proof of the Jordan curve theorem via the Brouwer fixed point
theorem, in Lean 4. The mathematics is Maehara's, published in 1984; the
formal development is this repository's, and it started from a submission to
a public benchmark rather than from nothing.

## References

The starting point was the `jordan_curve` problem of the
[lean-eval](https://github.com/leanprover/lean-eval) benchmark, which poses
the statement

```lean
theorem jordan_curve (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    EuclideanSpace ℝ (Fin 2)) (_hcont : Continuous r) (_hinj : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ)) = 2
```

and records four solutions. The one this library began from is
`rkirov/jordan_pick`, commit `ad2aa1f637609c212210888b4ad9e926c30debb4`, path
`submission/jordan_curve/Submission/`, released under the Apache License 2.0
— a copy of which sits beside this file.

* K. Maehara, *The Jordan curve theorem via the Brouwer fixed point theorem*,
  American Mathematical Monthly 91 (1984), 641–643.
* lean-eval, problem `jordan_curve`:
  <https://lean-lang.org/eval/problems/jordan_curve/>
* rkirov/jordan_pick, Apache 2.0: <https://github.com/rkirov/jordan_pick>

## What changed here

Everything except the mathematics. The four files that arrived became
seventeen, every declaration was renamed, and the interfaces were rebuilt:

* **Structure.** One 2589-line file became eleven, split along the seams the
  argument already had — the crossing lemma, the topology of the complement,
  separation, the normalized frame, path construction, and the two steps.
* **Names.** Every declaration now states what it says. `step_A_normalized`
  is `exists_bounded_component_of_normalized`; `crossing` is
  `transversal_paths_meet_in_rectangle`; `dvec`, `Acoef`, `discr`, `tparam`,
  `rhoPt` are `displacement`, `raySphereQuadA`, `raySphereDiscriminant`,
  `raySphereRoot`, `retractionPoint`. Eighty-one names, five hundred and
  seventy occurrences.
* **Interfaces.** The nested existential of fifteen conjuncts that carried
  Maehara's five distinguished points is now the structure
  `MaeharaConfiguration`, with seventeen derived facts proved on it once
  rather than re-derived in every proof that needs them. The rectangle, and
  the straight segment that one proof wrote out by hand five times, are named
  and proved once.
* **Imports.** `import Mathlib` is gone; each file names the modules it uses.
* **Documentation.** Every declaration carries a docstring tagged `**Math.**`,
  `**Eng.**` or `**Mixed.**`, which is where the mathematics is separated
  from the type-theoretic plumbing.
* **Toolchain.** Carried from Lean v4.31 to v4.32.2, which took two fixes: a
  `Continuous.subtype_mk` chain that now exceeds the `isDefEq` heartbeat
  limit, and a `continuous_const.smul` whose scalar argument no longer
  elaborates without being pinned.
* **Budget.** Both `set_option maxHeartbeats` are gone — not by raising a
  limit but by naming the constructions the proofs were repeating.
* **Warnings.** Zero, against 165 when the reorganisation began.

## What is verified

```
lake exe jordan-audit
```

Every declaration the hypergraph's cards name is present, and each depends on
exactly `propext`, `Classical.choice` and `Quot.sound` — no `sorryAx`. In
particular `BrouwerFPT`, which the argument carries as an explicit interface,
is discharged by `JordanCurve.Brouwer.brouwerFPT` inside these files, so the
final theorem is unconditional.

`JordanCurve/Anchor.lean` guards what the audit cannot see. It restates the
theorem independently, in Mathlib's own vocabulary, and stops compiling if
anything the argument passes through is weakened. It is never edited to make
it compile.

## Note on an inherited comment

`Root.lean`'s module comment said the file "is a work-in-progress with
`sorry`s". That was true of its ancestor in the tree it was extracted from
and is false here; the audit above is the check. The file no longer exists
under that name, and the claim went with it.
