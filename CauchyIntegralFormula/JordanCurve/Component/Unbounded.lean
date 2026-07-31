/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Component.Bounded

@[expose] public section

/-!
# Step B: the bounded component is unique

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** The Euclidean norm of an axis point `!₂[0,y]` equals `|y|`. -/
private lemma norm_axis_pt (y : ℝ) : ‖(!₂[(0:ℝ), y] : Plane)‖ = |y| := by
  have e0 : (!₂[(0:ℝ), y] : Plane) 0 = 0 := by simp
  have e1 : (!₂[(0:ℝ), y] : Plane) 1 = y := by simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1]
  simp [Real.sqrt_sq_eq_abs]

/-- **Math.** The upward axis ray `{p | p 0 = 0 ∧ c < p 1}` is unbounded. -/
private lemma axis_ray_up_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) 1 = |c| + |M| + 1 := by simp
  have hmem : (!₂[(0:ℝ), |c| + |M| + 1] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Ioi, hy1]; linarith [le_abs_self c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- **Math.** The downward axis ray `{p | p 0 = 0 ∧ p 1 < c}` is unbounded. -/
private lemma axis_ray_down_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) 1 = -(|c| + |M| + 1) := by simp
  have hmem : (!₂[(0:ℝ), -(|c| + |M| + 1)] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Iio, hy1]; linarith [neg_abs_le c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_axis_pt, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- **Math.** The complement of the normalized rectangle `[-1,1]×[-2,2]` is preconnected
(it is the union of four half-planes chained around the rectangle). -/
private lemma isPreconnected_rect_compl :
    IsPreconnected {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)} := by
  have cA : Convex ℝ {v : Plane | v 0 ∈ Iio (-1:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cB : Convex ℝ {v : Plane | v 0 ∈ Ioi (1:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cC : Convex ℝ {v : Plane | v 1 ∈ Iio (-2:ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  have cD : Convex ℝ {v : Plane | v 1 ∈ Ioi (2:ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  -- membership witnesses at the four "corners"
  have mAD_A : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Iio (-1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio, show (!₂[(-2:ℝ), 3] : Plane) 0 = -2 from by simp]; norm_num
  have mAD_D : (!₂[(-2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi, show (!₂[(-2:ℝ), 3] : Plane) 1 = 3 from by simp]; norm_num
  have mB_D : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi, show (!₂[(2:ℝ), 3] : Plane) 1 = 3 from by simp]; norm_num
  have mB_B : (!₂[(2:ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi, show (!₂[(2:ℝ), 3] : Plane) 0 = 2 from by simp]; norm_num
  have mC_B : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi, show (!₂[(2:ℝ), -3] : Plane) 0 = 2 from by simp]; norm_num
  have mC_C : (!₂[(2:ℝ), -3] : Plane) ∈ {v : Plane | v 1 ∈ Iio (-2:ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio, show (!₂[(2:ℝ), -3] : Plane) 1 = -3 from by simp]; norm_num
  have hAD : IsPreconnected ({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)}) :=
    cA.isPreconnected.union _ mAD_A mAD_D cD.isPreconnected
  have hADB : IsPreconnected (({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) :=
    hAD.union _ (Or.inr mB_D) mB_B cB.isPreconnected
  have hADBC : IsPreconnected ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) :=
    hADB.union _ (Or.inr mC_B) mC_C cC.isPreconnected
  have hEq : {v : Plane | ¬(v 0 ∈ Icc (-1:ℝ) 1 ∧ v 1 ∈ Icc (-2:ℝ) 2)}
      = ((({v : Plane | v 0 ∈ Iio (-1:ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2:ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1:ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2:ℝ)}) := by
    ext v
    simp only [mem_setOf_eq, mem_union, mem_Icc, mem_Iio, mem_Ioi, not_and_or, not_le]
    tauto
  rw [hEq]; exact hADBC

/-- **Math.** Straight segment from `P` to `Q`, reparametrized on `[-1,1]`. -/
private noncomputable def segP (P Q : Plane) : ℝ → Plane := fun t => P + ((t + 1) / 2) • (Q - P)

private lemma segP_cont (P Q : Plane) : Continuous (segP P Q) := by unfold segP; fun_prop

private lemma segP_neg1 (P Q : Plane) : segP P Q (-1) = P := by simp [segP]

private lemma segP_one (P Q : Plane) : segP P Q 1 = Q := by simp [segP]

private lemma segP_coord (P Q : Plane) (t : ℝ) (i : Fin 2) :
    segP P Q t i = P i + ((t + 1) / 2) * (Q i - P i) := by
  simp only [segP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

private lemma segP_dist_le (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) P ≤ dist Q P := by
  have hs : |(t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) P = |(t + 1) / 2| * dist Q P := by
    rw [segP, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |(t + 1) / 2| * dist Q P ≤ 1 * dist Q P :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist Q P := one_mul _

private lemma segP_dist_le' (P Q : Plane) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    dist (segP P Q t) Q ≤ dist P Q := by
  have hs : |1 - (t + 1) / 2| ≤ 1 := by
    rw [mem_Icc] at ht; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have heq : dist (segP P Q t) Q = |1 - (t + 1) / 2| * dist P Q := by
    rw [segP, dist_eq_norm,
      show P + ((t + 1) / 2) • (Q - P) - Q = (1 - (t + 1) / 2) • (P - Q) from by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  rw [heq]
  calc |1 - (t + 1) / 2| * dist P Q ≤ 1 * dist P Q :=
        mul_le_mul_of_nonneg_right hs dist_nonneg
    _ = dist P Q := one_mul _

/-- **Math.** A coordinate of a segment point lies in any interval containing both endpoints'
corresponding coordinates. -/
private lemma segP_coord_mem_Icc {P Q : Plane} (i : Fin 2) {lo hi : ℝ}
    (hP : P i ∈ Icc lo hi) (hQ : Q i ∈ Icc lo hi) {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    segP P Q t i ∈ Icc lo hi := by
  rw [mem_Icc] at hP hQ ht
  rw [segP_coord, mem_Icc]
  have hs0 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have hs1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  constructor
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.1] : (0:ℝ) ≤ Q i - lo),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.1] : (0:ℝ) ≤ P i - lo)]
  · nlinarith [mul_nonneg hs0 (by linarith [hQ.2] : (0:ℝ) ≤ hi - Q i),
      mul_nonneg (by linarith [hs1] : (0:ℝ) ≤ 1 - (t + 1) / 2) (by linarith [hP.2] : (0:ℝ) ≤ hi - P i)]

set_option maxHeartbeats 1600000 in
/-- **Math.** **Maehara Step B (normalized).** Uniqueness of the bounded component in
normalized coordinates (farthest pair at `!₂[-1,0]`, `!₂[1,0]`). Any bounded
component equals the `z₀`-component `U`, hence all bounded components coincide. -/
theorem step_B_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have ha0 : (!₂[(-1:ℝ), 0] : Plane) 0 = -1 := by simp
  have ha1 : (!₂[(-1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hb0 : (!₂[(1:ℝ), 0] : Plane) 0 = 1 := by simp
  have hb1 : (!₂[(1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hs0 : (!₂[(0:ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0:ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmr : m ∈ range r := hJnr hmJn
  have hlr : l ∈ range r := hJnr hlJn
  have hpr : p ∈ range r := hJsr hpJs
  have hqr : q ∈ range r := hJsr hqJs
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect hmr).2
  have hlE1 : l 1 ∈ Icc (-2:ℝ) 2 := (hErect hlr).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect hpr).2
  have hqE1 : q 1 ∈ Icc (-2:ℝ) 2 := (hErect hqr).2
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  have hz₀1lb : (-2:ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hmab : m ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hlab : l ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hl0, ha0, hb0] at hc; norm_num at hc)
  have hqab : q ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hq0, ha0, hb0] at hc; norm_num at hc)
  have hpab : p ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hp0, ha0, hb0] at hc; norm_num at hc)
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  -- interval facts
  have hIcc0x : (0:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc0y : (0:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm1x : (-1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc1x : (1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  -- the `z₀`-component `U`, the rectangle `E`
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUdef
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} with hEdef
  -- the open middle axis segment `(p,m)` lies in `U`
  set Mid : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} with hMiddef
  have hMidPC : IsPathConnected Mid :=
    isPathConnected_vertSeg 0 ((convex_Ioo (p 1) (m 1)).isPathConnected (Set.nonempty_Ioo.mpr hpm_lt))
  have hMidc : Mid ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (hmmin v h hv0) (not_le.2 hv1.2)
    · exact absurd (hpmax v h hv0 hv1.2.le) (not_le.2 hv1.1)
  have hz₀Mid : z₀ ∈ Mid :=
    ⟨hz₀0, by rw [hz₀1e]; exact ⟨by linarith [hpm_lt], by linarith [hpm_lt]⟩⟩
  have hMidU : Mid ⊆ U :=
    hMidPC.isConnected.isPreconnected.subset_connectedComponentIn hz₀Mid hMidc
  -- upward and downward axis rays lie in the complement
  set RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} with hRayNdef
  have hRayNPC : IsPathConnected RayN :=
    isPathConnected_vertSeg 0 ((convex_Ioi (l 1)).isPathConnected Set.nonempty_Ioi)
  have hRayNc : RayN ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr; exact absurd (hlmax v hvr hv0) (not_le.2 hv1)
  set RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} with hRaySdef
  have hRaySPC : IsPathConnected RayS :=
    isPathConnected_vertSeg 0 ((convex_Iio (q 1)).isPathConnected Set.nonempty_Iio)
  have hRaySc : RayS ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (le_trans (le_trans hqp hpm) (hmmin v h hv0)) (not_le.2 hv1)
    · exact absurd (hqmin v h hv0) (not_le.2 hv1)
  -- **KEY**: every bounded component equals `U`.
  have KEY : ∀ w ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ w) →
      connectedComponentIn (range r)ᶜ w = U := by
    intro w hw hwb
    by_contra hWne
    set W : Set Plane := connectedComponentIn (range r)ᶜ w with hWdef
    have hWsub : W ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
    have hwW : w ∈ W := mem_connectedComponentIn hw
    have hWpc : IsPathConnected W := isPathConnected_component r hcont hw
    -- `W` and `U` are disjoint
    have hWU_disj : Disjoint W U := by
      rw [Set.disjoint_left]
      intro v hvW hvU
      apply hWne
      rw [hWdef, connectedComponentIn_eq (hWdef ▸ hvW), hUdef]
      exact (connectedComponentIn_eq (hUdef ▸ hvU)).symm
    -- component-equation helper: any `v ∈ W` has component `= W`
    have compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn (range r)ᶜ v = W := by
      intro v hvW; rw [hWdef]; exact (connectedComponentIn_eq (hWdef ▸ hvW)).symm
    -- avoid lemmas
    have avoid_up : ∀ v : Plane, v 0 = 0 → l 1 ≤ v 1 → v ∉ W := by
      intro v hv0 hvl hvW
      rcases eq_or_lt_of_le hvl with h | h
      · have hveq : v = l := by ext i; fin_cases i <;> simp [hv0, hl0, h]
        exact hWsub hvW (by rw [hveq]; exact hlr)
      · have h1 := hRayNPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayN from ⟨hv0, h⟩) hRayNc
        exact axis_ray_up_unbounded (l 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_down : ∀ v : Plane, v 0 = 0 → v 1 ≤ q 1 → v ∉ W := by
      intro v hv0 hvq hvW
      rcases eq_or_lt_of_le hvq with h | h
      · have hveq : v = q := by ext i; fin_cases i <;> simp [hv0, hq0, h]
        exact hWsub hvW (by rw [hveq]; exact hqr)
      · have h1 := hRaySPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayS from ⟨hv0, h⟩) hRaySc
        exact axis_ray_down_unbounded (q 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_mid : ∀ v : Plane, v 0 = 0 → p 1 ≤ v 1 → v 1 ≤ m 1 → v ∉ W := by
      intro v hv0 hvp hvm hvW
      rcases eq_or_lt_of_le hvp with h | h
      · have hveq : v = p := by ext i; fin_cases i <;> simp [hv0, hp0, h]
        exact hWsub hvW (by rw [hveq]; exact hpr)
      · rcases eq_or_lt_of_le hvm with h' | h'
        · have hveq : v = m := by ext i; fin_cases i <;> simp [hv0, hm0, h']
          exact hWsub hvW (by rw [hveq]; exact hmr)
        · exact (Set.disjoint_left.mp hWU_disj hvW) (hMidU ⟨hv0, ⟨h, h'⟩⟩)
    -- `W ⊆ E` (a bounded component lies in the rectangle)
    have hWE : W ⊆ E := by
      intro v hvW
      by_contra hvE
      rw [hEdef, Set.mem_setOf_eq] at hvE
      have hvEc : v ∈ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := hvE
      have hEcc : {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} ⊆ (range r)ᶜ :=
        fun u hu hur => hu (hErect hur)
      have h1 := isPreconnected_rect_compl.subset_connectedComponentIn hvEc hEcc
      have hup : {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi (2:ℝ)}
          ⊆ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := by
        rintro u ⟨_, hu1⟩ ⟨_, hu2⟩
        rw [mem_Icc] at hu2; rw [mem_Ioi] at hu1; linarith [hu2.2]
      exact axis_ray_up_unbounded 2 (hwb.subset (subset_trans hup (compW hvW ▸ h1)))
    -- **spine path** `β : n → s`, top to bottom, missing `W`, inside `E`
    have hnl_cont : ContinuousOn (segP (!₂[(0:ℝ), 2]) l) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨lm, hlm_cont, hlm_a, hlm_b, hlm_mem⟩ :=
      arc_path (hpcJn.joinedIn l ⟨hlJn, hlab⟩ m ⟨hmJn, hmab⟩)
    have hmp_cont : ContinuousOn (segP m p) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨pq, hpq_cont, hpq_a, hpq_b, hpq_mem⟩ :=
      arc_path (hpcJs.joinedIn p ⟨hpJs, hpab⟩ q ⟨hqJs, hqab⟩)
    have hqs_cont : ContinuousOn (segP q (!₂[(0:ℝ), -2])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨β, hβcont, hβa, hβb, hβmem⟩ :=
      concatPath5 hnl_cont hlm_cont hmp_cont hpq_cont hqs_cont
        (by rw [segP_one, hlm_a]) (by rw [hlm_b, segP_neg1]) (by rw [segP_one, hpq_a])
        (by rw [hpq_b, segP_neg1])
    have hβE : ∀ t ∈ Icc (-1:ℝ) 1, β t 0 ∈ Icc (-1:ℝ) 1 ∧ β t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hn0]; exact hIcc0x) (by rw [hl0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 (by rw [hn1]; exact hIcc2y) hlE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hm0]; exact hIcc0x) (by rw [hp0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hmE1 hpE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hq0]; exact hIcc0x) (by rw [hs0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hqE1 (by rw [hs1]; exact hIccm2y) hu⟩
    have hβmiss : ∀ t ∈ Icc (-1:ℝ) 1, β t ∉ W := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_up _ ?_ ?_
        · rw [segP_coord, hn0, hl0]; ring
        · rw [segP_coord, hn1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hlE1.2]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_mid _ ?_ ?_ ?_
        · rw [segP_coord, hm0, hp0]; ring
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_down _ ?_ ?_
        · rw [segP_coord, hq0, hs0]; ring
        · rw [segP_coord, hs1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hqE1.1]
    -- `a, b ∈ closure W` (frontier of a component is the whole curve)
    have hfrW : frontier W = range r := by
      have hexists : ∃ y ∈ (range r)ᶜ,
          connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ w := by
        refine ⟨z₀, hz₀c, ?_⟩
        rw [← hUdef, ← hWdef]; exact fun h => hWne h.symm
      have hcbe := component_boundary_eq hbr hcont hinj hw hexists
      rwa [← hWdef] at hcbe
    have hafrW : (!₂[(-1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hm
    have hbfrW : (!₂[(1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hp
    have haclW : (!₂[(-1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hafrW
    have hbclW : (!₂[(1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hbfrW
    -- compact image of `β`, and small balls at `a, b` avoiding it
    set βimg : Set Plane := β '' Icc (-1:ℝ) 1 with hβimgdef
    have hβimg_closed : IsClosed βimg := (isCompact_Icc.image_of_continuousOn hβcont).isClosed
    have ha_notβ : (!₂[(-1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, hta⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hn0, hl0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hm0, hp0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hq0, hs0]; ring
        rw [ha0] at hcz; norm_num at hcz
    have hb_notβ : (!₂[(1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, htb⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hn0, hl0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hm0, hp0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hq0, hs0]; ring
        rw [hb0] at hcz; norm_num at hcz
    obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ ha_notβ
    obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ hb_notβ
    -- points of `W` near `a, b`
    rw [Metric.mem_closure_iff] at haclW hbclW
    obtain ⟨a₁, ha₁W, ha₁d⟩ := haclW εa hεa
    obtain ⟨b₁, hb₁W, hb₁d⟩ := hbclW εb hεb
    have ha₁E : a₁ 0 ∈ Icc (-1:ℝ) 1 ∧ a₁ 1 ∈ Icc (-2:ℝ) 2 := hWE ha₁W
    have hb₁E : b₁ 0 ∈ Icc (-1:ℝ) 1 ∧ b₁ 1 ∈ Icc (-2:ℝ) 2 := hWE hb₁W
    -- **path** `H : a → b`, left to right, inside `E`, missing `β`
    have hHp1_cont : ContinuousOn (segP (!₂[(-1:ℝ), 0]) a₁) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨Harc, hHarc_cont, hHarc_a, hHarc_b, hHarc_mem⟩ :=
      arc_path (hWpc.joinedIn a₁ ha₁W b₁ hb₁W)
    have hHp3_cont : ContinuousOn (segP b₁ (!₂[(1:ℝ), 0])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨H, hHcont, hHa, hHb, hHmem⟩ :=
      concatPath3 hHp1_cont hHarc_cont hHp3_cont
        (by rw [segP_one, hHarc_a]) (by rw [hHarc_b, segP_neg1])
    have hHa0 : H (-1) 0 = -1 := by rw [hHa, segP_neg1, ha0]
    have hHb0 : H 1 0 = 1 := by rw [hHb, segP_one, hb0]
    have hHE : ∀ t ∈ Icc (-1:ℝ) 1, H t 0 ∈ Icc (-1:ℝ) 1 ∧ H t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [ha0]; exact hIccm1x) ha₁E.1 hu,
          segP_coord_mem_Icc 1 (by rw [ha1]; exact hIcc0y) ha₁E.2 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hWE (hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 hb₁E.1 (by rw [hb0]; exact hIcc1x) hu,
          segP_coord_mem_Icc 1 hb₁E.2 (by rw [hb1]; exact hIcc0y) hu⟩
    have hHmiss : ∀ t ∈ Icc (-1:ℝ) 1, H t ∉ βimg := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP (!₂[(-1:ℝ), 0]) a₁ u ∈ Metric.ball (!₂[(-1:ℝ), 0] : Plane) εa := by
          rw [Metric.mem_ball]
          calc dist (segP (!₂[(-1:ℝ), 0]) a₁ u) (!₂[(-1:ℝ), 0])
                ≤ dist a₁ (!₂[(-1:ℝ), 0]) := segP_dist_le _ _ hu
            _ < εa := by rw [dist_comm]; exact ha₁d
        exact hballa hin hmemβ
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        obtain ⟨t', ht', ht'e⟩ := hmemβ
        exact hβmiss t' ht' (by rw [ht'e]; exact hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP b₁ (!₂[(1:ℝ), 0]) u ∈ Metric.ball (!₂[(1:ℝ), 0] : Plane) εb := by
          rw [Metric.mem_ball]
          calc dist (segP b₁ (!₂[(1:ℝ), 0]) u) (!₂[(1:ℝ), 0])
                ≤ dist b₁ (!₂[(1:ℝ), 0]) := segP_dist_le' _ _ hu
            _ < εb := by rw [dist_comm]; exact hb₁d
        exact hballb hin hmemβ
    -- reorient `β` bottom-to-top and cross with `H`
    set v : ℝ → Plane := fun t => β (-t) with hvdef
    have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) :=
      hβcont.comp continuous_neg.continuousOn (fun t ht => by
        rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht; rw [mem_Icc] at ht
      exact hβE (-t) (by rw [mem_Icc]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hv1 : v (-1) 1 = -2 := by show β (-(-1)) 1 = -2; rw [neg_neg, hβb, segP_one, hs1]
    have hv2 : v 1 1 = 2 := by show β (-1) 1 = 2; rw [hβa, segP_neg1, hn1]
    obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1) (by norm_num : (-2:ℝ) ≤ 2)
      H v hHcont hvcont hHE hvE hHa0 hHb0 hv1 hv2
    apply hHmiss s hs
    rw [heq]
    exact Set.mem_image_of_mem β (show (-t) ∈ Icc (-1:ℝ) 1 by
      rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  -- assemble: bounded components of `x, y` both equal `U`
  intro x hx y hy hxb hyb
  rw [KEY x hx hxb, KEY y hy hyb]

/-- **Math.** **Maehara Step B (geometric core).** Bounded components of `ℝ²∖J` are unique.
Reduced to the normalized version `step_B_normalized` via the farthest-pair
similarity `T`. -/
theorem step_B_bounded_unique (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  intro x hx y hy hxb hyb
  obtain ⟨a, ha, b, hb, hfar0, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0:ℝ) < 2 / dist a b := by positivity
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  have hrc : (range r')ᶜ = (T : Plane → Plane) '' (range r)ᶜ := by rw [hrange, himg]
  have hm' : (!₂[(-1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b :=
          mul_le_mul_of_nonneg_left (hfar0 z hz w hw) hcpos.le
      _ = 2 := by field_simp
  -- transport the two components forward by `T`
  have hTx : T x ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hx
  have hTy : T y ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hy
  have hccx : connectedComponentIn (range r')ᶜ (T x)
      = T '' connectedComponentIn (range r)ᶜ x := by
    rw [hrc]; exact (T.image_connectedComponentIn hx).symm
  have hccy : connectedComponentIn (range r')ᶜ (T y)
      = T '' connectedComponentIn (range r)ᶜ y := by
    rw [hrc]; exact (T.image_connectedComponentIn hy).symm
  have hTxb : IsBounded (connectedComponentIn (range r')ᶜ (T x)) := by
    rw [hccx]; exact (isBounded_image_scaling hcpos hscale _).mpr hxb
  have hTyb : IsBounded (connectedComponentIn (range r')ᶜ (T y)) := by
    rw [hccy]; exact (isBounded_image_scaling hcpos hscale _).mpr hyb
  have hEq := step_B_normalized hbr hr'cont hr'inj hm' hp' hfar'
    (T x) hTx (T y) hTy hTxb hTyb
  rw [hccx, hccy] at hEq
  exact Set.image_injective.mpr T.injective hEq

end JordanCurve
