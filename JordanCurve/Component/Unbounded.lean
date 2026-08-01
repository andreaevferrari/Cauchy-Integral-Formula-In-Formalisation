/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
module

public import JordanCurve.Component.Bounded

/-!
# Step B: the bounded component is unique

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** The Euclidean norm of an axis point `!₂[0,y]` equals `|y|`. -/
private lemma norm_of_point_on_vertical_axis (y : ℝ) : ‖(!₂[(0 : ℝ), y] : Plane)‖ = |y| := by
  have e0 : (!₂[(0 : ℝ), y] : Plane) 0 = 0 := by simp
  have e1 : (!₂[(0 : ℝ), y] : Plane) 1 = y := by simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1]
  simp [Real.sqrt_sq_eq_abs]

/-- **Math.** The upward axis ray `{p | p 0 = 0 ∧ c < p 1}` is unbounded. -/
private lemma axis_ray_up_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0 : ℝ), |c| + |M| + 1] : Plane) 1 = |c| + |M| + 1 := by simp
  have hmem : (!₂[(0 : ℝ), |c| + |M| + 1] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Ioi, hy1]; linarith [le_abs_self c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_of_point_on_vertical_axis,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- **Math.** The downward axis ray `{p | p 0 = 0 ∧ p 1 < c}` is unbounded. -/
private lemma axis_ray_down_unbounded (c : ℝ) :
    ¬ IsBounded {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : Plane)
  have hy1 : (!₂[(0 : ℝ), -(|c| + |M| + 1)] : Plane) 1 = -(|c| + |M| + 1) := by simp
  have hmem : (!₂[(0 : ℝ), -(|c| + |M| + 1)] : Plane) ∈ {p : Plane | p 0 = 0 ∧ p 1 ∈ Iio c} := by
    refine ⟨by simp, ?_⟩
    rw [mem_Iio, hy1]; linarith [neg_abs_le c, abs_nonneg M]
  have hin := hM hmem
  rw [mem_closedBall_zero_iff, norm_of_point_on_vertical_axis, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| + |M| + 1)] at hin
  linarith [le_abs_self M, abs_nonneg c]

/-- **Math.** The complement of the normalized rectangle `[-1,1]×[-2,2]` is preconnected
(it is the union of four half-planes chained around the rectangle). -/
private lemma isPreconnected_compl_rectangle :
    IsPreconnected {v : Plane | ¬(v 0 ∈ Icc (-1 : ℝ) 1 ∧ v 1 ∈ Icc (-2 : ℝ) 2)} := by
  have cA : Convex ℝ {v : Plane | v 0 ∈ Iio (-1 : ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cB : Convex ℝ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
  have cC : Convex ℝ {v : Plane | v 1 ∈ Iio (-2 : ℝ)} :=
    (convex_Iio _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  have cD : Convex ℝ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} :=
    (convex_Ioi _).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
  -- membership witnesses at the four "corners"
  have mAD_A : (!₂[(-2 : ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Iio (-1 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio]; norm_num
  have mAD_D : (!₂[(-2 : ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mB_D : (!₂[(2 : ℝ), 3] : Plane) ∈ {v : Plane | v 1 ∈ Ioi (2 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mB_B : (!₂[(2 : ℝ), 3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mC_B : (!₂[(2 : ℝ), -3] : Plane) ∈ {v : Plane | v 0 ∈ Ioi (1 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Ioi]; norm_num
  have mC_C : (!₂[(2 : ℝ), -3] : Plane) ∈ {v : Plane | v 1 ∈ Iio (-2 : ℝ)} := by
    simp only [Set.mem_setOf_eq, mem_Iio]; norm_num
  have hAD : IsPreconnected ({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)}) :=
    cA.isPreconnected.union _ mAD_A mAD_D cD.isPreconnected
  have hADB : IsPreconnected (({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) :=
    hAD.union _ (Or.inr mB_D) mB_B cB.isPreconnected
  have hADBC : IsPreconnected ((({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2 : ℝ)}) :=
    hADB.union _ (Or.inr mC_B) mC_C cC.isPreconnected
  have hEq : {v : Plane | ¬(v 0 ∈ Icc (-1 : ℝ) 1 ∧ v 1 ∈ Icc (-2 : ℝ) 2)}
      = ((({v : Plane | v 0 ∈ Iio (-1 : ℝ)} ∪ {v : Plane | v 1 ∈ Ioi (2 : ℝ)})
      ∪ {v : Plane | v 0 ∈ Ioi (1 : ℝ)}) ∪ {v : Plane | v 1 ∈ Iio (-2 : ℝ)}) := by
    ext v
    simp only [mem_setOf_eq, mem_union, mem_Icc, mem_Iio, mem_Ioi, not_and_or, not_le]
    tauto
  rw [hEq]; exact hADBC


/-- **Math.** **Maehara Step B (normalized).** Uniqueness of the bounded component in
normalized coordinates (farthest pair at `!₂[-1,0]`, `!₂[1,0]`). Any bounded
component equals the `z₀`-component `U`, hence all bounded components coincide. -/
theorem bounded_component_unique_of_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  classical
  obtain ⟨cfg⟩ := exists_maehara_configuration hbr hcont hinj hm hp hfar
  have hRectSub := cfg.subset_rectangle
  have hUnion := cfg.union_eq
  have hInter := cfg.inter_eq
  have hpcJn := cfg.isPathConnected_northern
  have hpcJs := cfg.isPathConnected_southern
  have hJoinJn := cfg.joinedIn_northern
  have hJoinJs := cfg.joinedIn_southern
  have hlJn := cfg.topOfNorthern_mem
  have hl0 := cfg.topOfNorthern_coord_zero
  have hlmax := cfg.topOfNorthern_max
  have hmJn := cfg.bottomOfNorthern_mem
  have hm0 := cfg.bottomOfNorthern_coord_zero
  have hmmin := cfg.bottomOfNorthern_min
  have hpJs := cfg.topOfSouthernBelow_mem
  have hp0 := cfg.topOfSouthernBelow_coord_zero
  have hpm := cfg.topOfSouthernBelow_le
  have hpmax := cfg.topOfSouthernBelow_max
  have hqJs := cfg.bottomOfSouthern_mem
  have hq0 := cfg.bottomOfSouthern_coord_zero
  have hqmin := cfg.bottomOfSouthern_min
  have hml := cfg.bottomOfNorthern_le_topOfNorthern
  have hqp := cfg.bottomOfSouthern_le_topOfSouthernBelow
  have hpz₀ := cfg.topOfSouthernBelow_le_midpoint
  have hz₀m := cfg.midpoint_le_bottomOfNorthern
  set J_n := cfg.northern with hJndef
  set J_s := cfg.southern with hJsdef
  set l := cfg.topOfNorthern with hldef
  set m := cfg.bottomOfNorthern with hmdef
  set p := cfg.topOfSouthernBelow with hpdef
  set q := cfg.bottomOfSouthern with hqdef
  set z₀ := cfg.midpoint with hz₀setdef
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have hmr : m ∈ range r := hJnr hmJn
  have hlr : l ∈ range r := hJnr hlJn
  have hpr : p ∈ range r := hJsr hpJs
  have hqr : q ∈ range r := hJsr hqJs
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp cfg.topOfSouthernBelow_lt_bottomOfNorthern
  have hz₀1lb : (-2 : ℝ) ≤ z₀ 1 := le_of_lt
    (lt_of_le_of_lt cfg.topOfSouthernBelow_height_mem.1 cfg.topOfSouthernBelow_lt_midpoint)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt
    (lt_of_lt_of_le cfg.midpoint_lt_bottomOfNorthern cfg.bottomOfNorthern_height_mem.2)
  have hmab : m ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.bottomOfNorthern_coord_zero
  have hlab : l ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.topOfNorthern_coord_zero
  have hqab : q ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.bottomOfSouthern_coord_zero
  have hpab : p ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.topOfSouthernBelow_coord_zero
  -- interval facts
  have hIcc0x : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc0y : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2 : ℝ) ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm1x : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc1x : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; norm_num
  -- the `z₀`-component `U`, the rectangle `E`
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUdef
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn cfg.midpoint_not_mem_range
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} with hEdef
  -- the open middle axis segment `(p,m)` lies in `U`
  set Mid : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} with hMiddef
  have hMidPC : IsPathConnected Mid :=
    isPathConnected_verticalSegment 0
      ((convex_Ioo (p 1) (m 1)).isPathConnected
        (Set.nonempty_Ioo.mpr cfg.topOfSouthernBelow_lt_bottomOfNorthern))
  have hMidc : Mid ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (hmmin v h hv0) (not_le.2 hv1.2)
    · exact absurd (hpmax v h hv0 hv1.2.le) (not_le.2 hv1.1)
  have hz₀Mid : z₀ ∈ Mid :=
    ⟨cfg.midpoint_coord_zero, by
      rw [cfg.midpoint_coord_one]
      exact ⟨by linarith [cfg.topOfSouthernBelow_lt_bottomOfNorthern],
        by linarith [cfg.topOfSouthernBelow_lt_bottomOfNorthern]⟩⟩
  have hMidU : Mid ⊆ U :=
    hMidPC.isConnected.isPreconnected.subset_connectedComponentIn hz₀Mid hMidc
  -- upward and downward axis rays lie in the complement
  set RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} with hRayNdef
  have hRayNPC : IsPathConnected RayN :=
    isPathConnected_verticalSegment 0 ((convex_Ioi (l 1)).isPathConnected Set.nonempty_Ioi)
  have hRayNc : RayN ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr; exact absurd (hlmax v hvr hv0) (not_le.2 hv1)
  set RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} with hRaySdef
  have hRaySPC : IsPathConnected RayS :=
    isPathConnected_verticalSegment 0 ((convex_Iio (q 1)).isPathConnected Set.nonempty_Iio)
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
      have hvEc : v ∈ {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} := hvE
      have hEcc : {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} ⊆ (range r)ᶜ :=
        fun u hu hur => hu (hErect hur)
      have h1 := isPreconnected_compl_rectangle.subset_connectedComponentIn hvEc hEcc
      have hup : {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi (2 : ℝ)}
          ⊆ {u : Plane | ¬(u 0 ∈ Icc (-1 : ℝ) 1 ∧ u 1 ∈ Icc (-2 : ℝ) 2)} := by
        rintro u ⟨_, hu1⟩ ⟨_, hu2⟩
        rw [mem_Icc] at hu2; rw [mem_Ioi] at hu1; linarith [hu2.2]
      exact axis_ray_up_unbounded 2 (hwb.subset (subset_trans hup (compW hvW ▸ h1)))
    -- **spine path** `β : n → s`, top to bottom, missing `W`, inside `E`
    have hnl_cont : ContinuousOn (segmentParam (axisTop) l) (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    obtain ⟨lm, hlm_cont, hlm_a, hlm_b, hlm_mem⟩ :=
      path_reparametrized_on_neg_one_one (hpcJn.joinedIn l ⟨hlJn, hlab⟩ m ⟨hmJn, hmab⟩)
    have hmp_cont : ContinuousOn (segmentParam m p) (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    obtain ⟨pq, hpq_cont, hpq_a, hpq_b, hpq_mem⟩ :=
      path_reparametrized_on_neg_one_one (hpcJs.joinedIn p ⟨hpJs, hpab⟩ q ⟨hqJs, hqab⟩)
    have hqs_cont : ContinuousOn (segmentParam q (axisBottom)) (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    obtain ⟨β, hβcont, hβa, hβb, hβmem⟩ :=
      concatPath5 hnl_cont hlm_cont hmp_cont hpq_cont hqs_cont
        (by rw [segmentParam_one, hlm_a]) (by rw [hlm_b,
          segmentParam_neg1]) (by rw [segmentParam_one, hpq_a])
        (by rw [hpq_b, segmentParam_neg1])
    have hβE : ∀ t ∈ Icc (-1 : ℝ) 1, β t 0 ∈ Icc (-1 : ℝ) 1 ∧ β t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segmentParam_coord_mem_Icc 0 (by rw [axisTop_coord_zero]; exact hIcc0x)
          (by rw [hl0]; exact hIcc0x) hu,
          segmentParam_coord_mem_Icc 1 (by rw [axisTop_coord_one]; exact hIcc2y)
            cfg.topOfNorthern_height_mem hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segmentParam_coord_mem_Icc 0 (by rw [hm0]; exact hIcc0x)
          (by rw [hp0]; exact hIcc0x) hu,
          segmentParam_coord_mem_Icc 1 cfg.bottomOfNorthern_height_mem
            cfg.topOfSouthernBelow_height_mem hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segmentParam_coord_mem_Icc 0 (by rw [hq0]; exact hIcc0x)
          (by rw [axisBottom_coord_zero]; exact hIcc0x) hu,
          segmentParam_coord_mem_Icc 1 cfg.bottomOfSouthern_height_mem
            (by rw [axisBottom_coord_one]; exact hIccm2y) hu⟩
    have hβmiss : ∀ t ∈ Icc (-1 : ℝ) 1, β t ∉ W := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_up _ ?_ ?_
        · rw [segmentParam_coord, axisTop_coord_zero, hl0]; ring
        · rw [segmentParam_coord, axisTop_coord_one]; rw [mem_Icc] at hu; nlinarith [hu.1,
          hu.2, cfg.topOfNorthern_height_mem.2]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_mid _ ?_ ?_ ?_
        · rw [segmentParam_coord, hm0, hp0]; ring
        · rw [segmentParam_coord]; rw [mem_Icc] at hu; nlinarith
          [hu.1, hu.2, cfg.topOfSouthernBelow_lt_bottomOfNorthern.le]
        · rw [segmentParam_coord]; rw [mem_Icc] at hu; nlinarith
          [hu.1, hu.2, cfg.topOfSouthernBelow_lt_bottomOfNorthern.le]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_down _ ?_ ?_
        · rw [segmentParam_coord, hq0, axisBottom_coord_zero]; ring
        · rw [segmentParam_coord, axisBottom_coord_one]; rw [mem_Icc] at hu; nlinarith [hu.1,
          hu.2, cfg.bottomOfSouthern_height_mem.1]
    -- `a, b ∈ closure W` (frontier of a component is the whole curve)
    have hfrW : frontier W = range r := by
      have hexists : ∃ y ∈ (range r)ᶜ,
          connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ w := by
        refine ⟨z₀, cfg.midpoint_not_mem_range, ?_⟩
        rw [← hUdef, ← hWdef]; exact fun h => hWne h.symm
      have hcbe := component_boundary_eq hbr hcont hinj hw hexists
      rwa [← hWdef] at hcbe
    have hafrW : normalizedLeftEnd ∈ frontier W := by rw [hfrW]; exact hm
    have hbfrW : normalizedRightEnd ∈ frontier W := by rw [hfrW]; exact hp
    have haclW : normalizedLeftEnd ∈ closure W := frontier_subset_closure hafrW
    have hbclW : normalizedRightEnd ∈ closure W := frontier_subset_closure hbfrW
    -- compact image of `β`, and small balls at `a, b` avoiding it
    set βimg : Set Plane := β '' Icc (-1 : ℝ) 1 with hβimgdef
    have hβimg_closed : IsClosed βimg := (isCompact_Icc.image_of_continuousOn hβcont).isClosed
    have ha_notβ : normalizedLeftEnd ∉ βimg := by
      rintro ⟨t, ht, hta⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedLeftEnd 0 = 0 := by
          rw [← hta, ← hue, segmentParam_coord, axisTop_coord_zero, hl0]; ring
        rw [normalizedLeftEnd_coord_zero] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedLeftEnd 0 = 0 := by
          rw [← hta, ← hue, segmentParam_coord, hm0, hp0]; ring
        rw [normalizedLeftEnd_coord_zero] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedLeftEnd 0 = 0 := by
          rw [← hta, ← hue, segmentParam_coord, hq0, axisBottom_coord_zero]; ring
        rw [normalizedLeftEnd_coord_zero] at hcz; norm_num at hcz
    have hb_notβ : normalizedRightEnd ∉ βimg := by
      rintro ⟨t, ht, htb⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedRightEnd 0 = 0 := by
          rw [← htb, ← hue, segmentParam_coord, axisTop_coord_zero, hl0]; ring
        rw [normalizedRightEnd_coord_zero] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedRightEnd 0 = 0 := by
          rw [← htb, ← hue, segmentParam_coord, hm0, hp0]; ring
        rw [normalizedRightEnd_coord_zero] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : normalizedRightEnd 0 = 0 := by
          rw [← htb, ← hue, segmentParam_coord, hq0, axisBottom_coord_zero]; ring
        rw [normalizedRightEnd_coord_zero] at hcz; norm_num at hcz
    obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ ha_notβ
    obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ hb_notβ
    -- points of `W` near `a, b`
    rw [Metric.mem_closure_iff] at haclW hbclW
    obtain ⟨a₁, ha₁W, ha₁d⟩ := haclW εa hεa
    obtain ⟨b₁, hb₁W, hb₁d⟩ := hbclW εb hεb
    have ha₁E : a₁ 0 ∈ Icc (-1 : ℝ) 1 ∧ a₁ 1 ∈ Icc (-2 : ℝ) 2 := hWE ha₁W
    have hb₁E : b₁ 0 ∈ Icc (-1 : ℝ) 1 ∧ b₁ 1 ∈ Icc (-2 : ℝ) 2 := hWE hb₁W
    -- **path** `H : a → b`, left to right, inside `E`, missing `β`
    have hHp1_cont : ContinuousOn (segmentParam (normalizedLeftEnd) a₁) (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    obtain ⟨Harc, hHarc_cont, hHarc_a, hHarc_b, hHarc_mem⟩ :=
      path_reparametrized_on_neg_one_one (hWpc.joinedIn a₁ ha₁W b₁ hb₁W)
    have hHp3_cont : ContinuousOn (segmentParam b₁ (normalizedRightEnd)) (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    obtain ⟨H, hHcont, hHa, hHb, hHmem⟩ :=
      concatPath3 hHp1_cont hHarc_cont hHp3_cont
        (by rw [segmentParam_one, hHarc_a]) (by rw [hHarc_b, segmentParam_neg1])
    have hHa0 : H (-1) 0 = -1 := by rw [hHa, segmentParam_neg1, normalizedLeftEnd_coord_zero]
    have hHb0 : H 1 0 = 1 := by rw [hHb, segmentParam_one, normalizedRightEnd_coord_zero]
    have hHE : ∀ t ∈ Icc (-1 : ℝ) 1, H t 0 ∈ Icc (-1 : ℝ) 1 ∧ H t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segmentParam_coord_mem_Icc 0
          (by rw [normalizedLeftEnd_coord_zero]; exact hIccm1x) ha₁E.1 hu,
          segmentParam_coord_mem_Icc 1
            (by rw [normalizedLeftEnd_coord_one]; exact hIcc0y) ha₁E.2 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hWE (hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segmentParam_coord_mem_Icc 0 hb₁E.1
          (by rw [normalizedRightEnd_coord_zero]; exact hIcc1x) hu,
          segmentParam_coord_mem_Icc 1 hb₁E.2
            (by rw [normalizedRightEnd_coord_one]; exact hIcc0y) hu⟩
    have hHmiss : ∀ t ∈ Icc (-1 : ℝ) 1, H t ∉ βimg := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segmentParam (normalizedLeftEnd) a₁ u ∈ Metric.ball normalizedLeftEnd εa :=
          by
          rw [Metric.mem_ball]
          calc dist (segmentParam (normalizedLeftEnd) a₁ u) (normalizedLeftEnd)
                ≤ dist a₁ (normalizedLeftEnd) := segmentParam_dist_to_start_le _ _ hu
            _ < εa := by rw [dist_comm]; exact ha₁d
        exact hballa hin hmemβ
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        obtain ⟨t', ht', ht'e⟩ := hmemβ
        exact hβmiss t' ht' (by rw [ht'e]; exact hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segmentParam b₁ (normalizedRightEnd) u ∈ Metric.ball normalizedRightEnd εb :=
          by
          rw [Metric.mem_ball]
          calc dist (segmentParam b₁ (normalizedRightEnd) u) (normalizedRightEnd)
                ≤ dist b₁ (normalizedRightEnd) := segmentParam_dist_to_end_le _ _ hu
            _ < εb := by rw [dist_comm]; exact hb₁d
        exact hballb hin hmemβ
    -- reorient `β` bottom-to-top and cross with `H`
    set v : ℝ → Plane := fun t => β (-t) with hvdef
    have hvcont : ContinuousOn v (Icc (-1 : ℝ) 1) :=
      hβcont.comp continuous_neg.continuousOn (fun t ht => by
        rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc (-1 : ℝ) 1 ∧ v t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht; rw [mem_Icc] at ht
      exact hβE (-t) (by rw [mem_Icc]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hv1 : v (-1) 1 = -2 := by
      change β (-(-1)) 1 = -2
      rw [neg_neg, hβb, segmentParam_one, axisBottom_coord_one]
    have hv2 : v 1 1 = 2 := by
      change β (-1) 1 = 2
      rw [hβa, segmentParam_neg1, axisTop_coord_one]
    obtain ⟨s, hs, t, ht, heq⟩ :=
      transversal_paths_meet_in_rectangle hbr
        (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (-2 : ℝ) ≤ 2)
      H v hHcont hvcont hHE hvE hHa0 hHb0 hv1 hv2
    apply hHmiss s hs
    rw [heq]
    exact Set.mem_image_of_mem β (show (-t) ∈ Icc (-1 : ℝ) 1 by
      rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  -- assemble: bounded components of `x, y` both equal `U`
  intro x hx y hy hxb hyb
  rw [KEY x hx hxb, KEY y hy hyb]

/-- **Math.** **Maehara Step B (geometric core).** Bounded components of `ℝ²∖J` are unique.
Reduced to the normalized version `bounded_component_unique_of_normalized` via the farthest-pair
similarity `T`. -/
theorem bounded_component_unique (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  intro x hx y hy hxb hyb
  obtain ⟨a, ha, b, hb, hfar0, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity_normalizing_farthest_pair hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0 : ℝ) < 2 / dist a b := by positivity
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  have hrc : (range r')ᶜ = (T : Plane → Plane) '' (range r)ᶜ := by rw [hrange, himg]
  have hm' : normalizedLeftEnd ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : normalizedRightEnd ∈ range r' := by
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
  have hEq := bounded_component_unique_of_normalized hbr hr'cont hr'inj hm' hp' hfar'
    (T x) hTx (T y) hTy hTxb hTyb
  rw [hccx, hccy] at hEq
  exact Set.image_injective.mpr T.injective hEq

end JordanCurve
