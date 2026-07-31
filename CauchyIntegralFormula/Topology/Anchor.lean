/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Main

/-!
# Regression anchor for the Jordan curve theorem

The Jordan curve development is being reorganised, and a reorganisation can
fail in two ways. `lake exe cif-audit` catches the first: a proof that has
acquired an axiom it should not have, `sorryAx` above all. It cannot catch
the second — a statement quietly weakened along the way, by an extracted
lemma that assumes slightly more than the original, or a hypothesis added
where the argument got hard. Such a library still builds, still audits
clean, and no longer proves what it claims.

This file is the guard against that. It restates the theorem **verbatim and
independently**, in the exact form the lean-eval benchmark poses it, and
proves it from the library. Nothing is imported into the statement below
from the development — it is written out in full, in Mathlib's own
vocabulary. If a refactor weakens anything the argument passes through, the
term-mode proof here stops typechecking, and the failure is a build failure
rather than a silent one.

The rule that goes with the file: **it is never edited to make it compile.**
If it breaks, the refactor broke something, and the refactor is what gets
fixed.
-/

@[expose] public section

namespace CauchyIntegralFormula.Topology

/-- **Math.** The Jordan curve theorem, stated independently of the
development that proves it: for every continuous injection of the unit
circle into the plane, the complement of its image has exactly two connected
components.

This is the anchor described in the module docstring — a regression test in
theorem form, not a result this file contributes. -/
theorem jordan_curve_anchor
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 :=
  JordanCurve.jordan_curve r hcont hinj

/-- **Math.** The bounded/unbounded split, which is what `def-inside-of-path`
rests on: the count of two components does not by itself say which of them is
bounded, and "inside" is defined as the bounded one.

Anchored here for the same reason and under the same rule as
`jordan_curve_anchor`. -/
theorem jordan_curve_unbounded_anchor
    {r : Metric.sphere (0 : JordanCurve.Plane) 1 → JordanCurve.Plane}
    (hcont : Continuous r) :
    ∃ x ∈ (Set.range r)ᶜ,
      ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) :=
  JordanCurve.exists_unbounded_component r hcont

end CauchyIntegralFormula.Topology
