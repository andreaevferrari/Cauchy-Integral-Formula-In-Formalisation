/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
module

public import JordanCurve.Normalization.Rectangle

/-!
# The straight segment, parametrised on `[-1,1]`

Every path this development builds is a concatenation of pieces, and most of
those pieces are straight segments. They are all parametrised on `[-1,1]`,
because that is the interval the crossing lemma works over.

The construction was written out by hand five times inside one proof and
once, named, inside another. It is named here once: `segmentParam P Q` runs
from `P` at `-1` to `Q` at `1`, and the lemmas below give its continuity, its
endpoints, its coordinates, the two distance bounds, and the fact that it
stays inside a box its endpoints are in.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** Straight segment from `P` to `Q`, reparametrized on `[-1,1]`. -/
noncomputable def segmentParam (P Q : Plane) : ℝ → Plane :=
  fun t => P + ((t + 1) / 2) • (Q - P)

lemma segmentParam_cont (P Q : Plane) : Continuous (segmentParam P Q) :=
  by unfold segmentParam; fun_prop

lemma segmentParam_neg1 (P Q : Plane) : segmentParam P Q (-1) = P := by simp [segmentParam]

lemma segmentParam_one (P Q : Plane) : segmentParam P Q 1 = Q := by simp [segmentParam]

lemma segmentParam_coord (P Q : Plane) (t : ℝ) (i : Fin 2) :
    segmentParam P Q t i = P i + ((t + 1) / 2) * (Q i - P i) := by
  simp only [segmentParam, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

lemma segmentParam_dist_to_start_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    dist (segmentParam P Q t) P ≤ dist Q P := by
  have hs : |(t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segmentParam P Q t) P = |(t + 1) / 2| * dist Q P := by
    rw [segmentParam, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      ← dist_eq_norm]
  rw [heq]
  calc |(t + 1) / 2| * dist Q P ≤ 1 * dist Q P :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist Q P := one_mul _

lemma segmentParam_dist_to_end_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    dist (segmentParam P Q t) Q ≤ dist P Q := by
  have hs : |1 - (t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segmentParam P Q t) Q = |1 - (t + 1) / 2| * dist P Q := by
    rw [segmentParam, dist_eq_norm,
      show P + ((t + 1) / 2) • (Q - P) - Q = (1 - (t + 1) / 2) • (P - Q) from by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |1 - (t + 1) / 2| * dist P Q ≤ 1 * dist P Q :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist P Q := one_mul _

/-- **Math.** A coordinate of a segment point lies in any interval containing both endpoints'
corresponding coordinates. -/
lemma segmentParam_coord_mem_Icc {P Q : Plane} (i : Fin 2) {lo hi : ℝ}
    (hP : P i ∈ Icc lo hi) (hQ : Q i ∈ Icc lo hi) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    segmentParam P Q t i ∈ Icc lo hi := by
  rw [mem_Icc] at hP hQ ht
  rw [segmentParam_coord, mem_Icc]
  have hs0 : (0 : ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have hs1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.1] : (0 : ℝ) ≤ Q i - lo),
      mul_nonneg (by linarith [hs1] : (0 : ℝ) ≤ 1 - (t + 1) / 2)
        (by linarith [hP.1] : (0 : ℝ) ≤ P i - lo)]
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.2] : (0 : ℝ) ≤ hi - Q i),
      mul_nonneg (by linarith [hs1] : (0 : ℝ) ≤ 1 - (t + 1) / 2)
        (by linarith [hP.2] : (0 : ℝ) ≤ hi - P i)]

end JordanCurve
