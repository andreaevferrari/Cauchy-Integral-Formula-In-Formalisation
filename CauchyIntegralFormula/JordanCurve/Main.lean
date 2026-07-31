/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Component.Unbounded

/-!
# The Jordan curve theorem

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** The Jordan curve theorem reduced to Brouwer (Maehara). The eval `jordan_curve`
follows by discharging `BrouwerFPT`. Given the two geometric core facts — existence
(`step_A_exists_bounded`) and uniqueness (`step_B_bounded_unique`) of a bounded
component — together with the unique unbounded component (`exists_unbounded_component`,
`unbounded_component_unique`), the complement has exactly two components. -/
theorem jordan_curve_of_brouwer (hbr : BrouwerFPT)
    (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 := by
  -- The unbounded component `x₀` and a bounded component `x₁`.
  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  set a : ↥((range r)ᶜ) := ⟨x₀, hx₀S⟩ with ha
  set b : ↥((range r)ᶜ) := ⟨x₁, hx₁S⟩ with hb
  -- The two components are distinct: one unbounded, one bounded.
  have hne : connectedComponentIn (range r)ᶜ x₀ ≠ connectedComponentIn (range r)ᶜ x₁ := by
    intro heq
    exact hx₀u (heq ▸ hx₁b)
  have hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b :=
    (Counting.connectedComponents_subtype_eq_iff hx₀S hx₁S).not.mpr hne
  -- Every component is either the bounded one (`= b`) or the unbounded one (`= a`).
  have hcover : ∀ z : ↥((range r)ᶜ),
      ConnectedComponents.mk z = ConnectedComponents.mk a
        ∨ ConnectedComponents.mk z = ConnectedComponents.mk b := by
    intro z
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z.val)
    · right
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₁S).mpr
        (step_B_bounded_unique hbr hcont hinj z.val z.2 x₁ hx₁S hzb hx₁b)
    · left
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₀S).mpr
        (unbounded_component_unique r hcont hzb hx₀u)
  exact Counting.nat_card_connectedComponents_eq_two a b hab hcover

/-- **Math.** **Jordan curve theorem** (the eval statement). -/
theorem jordan_curve
    (r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 := by
  -- Brouwer FPT for the plane, built from scratch in `JordanCurve.Brouwer`
  -- (circle non-nullhomotopy via Mathlib's covering-space lifting → no-retraction
  -- → disk Brouwer → convex-compact).
  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  exact jordan_curve_of_brouwer hbr r _hcont _hinj

end JordanCurve
