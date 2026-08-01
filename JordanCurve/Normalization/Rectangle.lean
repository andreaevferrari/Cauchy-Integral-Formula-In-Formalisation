/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
module

public import JordanCurve.Normalization.Setup

/-!
# The normalized rectangle

After the farthest pair has been moved to `!₂[-1,0]` and `!₂[1,0]`, the whole
curve lies in `[-1,1] × [-2,2]` and every later argument takes place inside
that box. This file names the box, names its interior, and proves the four
facts about them that the separation argument uses: bounded, closed, open,
and one contained in the other.

None of it is about Jordan curves — it is the elementary topology of a
rectangle in the plane, and it is stated here once rather than reproved
inside each of the two long arguments that need it.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** The normalized rectangle is bounded: it sits inside the closed
ball of radius `3` about the origin, since `1² + 2² = 5 ≤ 9`. -/
theorem isBounded_normalizedRectangle : IsBounded normalizedRectangle := by
  apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 3)).subset
  intro z hz
  rw [Metric.mem_closedBall]
  have hz1 := hz.1; have hz2 := hz.2; rw [mem_Icc] at hz1 hz2
  have hsq : dist z (0 : Plane) ^ 2 ≤ 9 := by
    rw [dist_sq_eq_sum_coord_sq, show (0 : Plane) 0 = 0 from by simp,
      show (0 : Plane) 1 = 0 from by simp]
    nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
  nlinarith [dist_nonneg (x := z) (y := (0 : Plane)), hsq]

/-- **Eng.** Taking the first coordinate is continuous. -/
theorem continuous_coord_zero : Continuous (fun z : Plane => z 0) := by fun_prop

/-- **Eng.** Taking the second coordinate is continuous. -/
theorem continuous_coord_one : Continuous (fun z : Plane => z 1) := by fun_prop

/-- **Math.** The normalized rectangle is closed, being the intersection of two
preimages of closed intervals under the coordinate maps. -/
theorem isClosed_normalizedRectangle : IsClosed normalizedRectangle := by
  have hEq : normalizedRectangle = (fun z : Plane => z 0) ⁻¹' Icc (-1 : ℝ) 1
      ∩ (fun z : Plane => z 1) ⁻¹' Icc (-2 : ℝ) 2 := by
    ext w; simp only [normalizedRectangle, mem_setOf_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isClosed_Icc.preimage continuous_coord_zero).inter
    (isClosed_Icc.preimage continuous_coord_one)

/-- **Math.** The open rectangle is open, for the same reason with open
intervals. -/
theorem isOpen_openNormalizedRectangle : IsOpen openNormalizedRectangle := by
  have hEq : openNormalizedRectangle = (fun z : Plane => z 0) ⁻¹' Ioo (-1 : ℝ) 1
      ∩ (fun z : Plane => z 1) ⁻¹' Ioo (-2 : ℝ) 2 := by
    ext w; simp only [openNormalizedRectangle, mem_setOf_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isOpen_Ioo.preimage continuous_coord_zero).inter
    (isOpen_Ioo.preimage continuous_coord_one)

/-- **Math.** The open rectangle is contained in the closed one. -/
theorem openNormalizedRectangle_subset :
    openNormalizedRectangle ⊆ normalizedRectangle :=
  fun _ hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩

/-- **Math.** After normalization the curve lies in the rectangle. This is
`normalized_subset_rectangle` phrased with the name rather than the set
comprehension it unfolds to. -/
theorem range_subset_normalizedRectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    range r ⊆ normalizedRectangle :=
  normalized_subset_rectangle hm hp hfar

end JordanCurve
