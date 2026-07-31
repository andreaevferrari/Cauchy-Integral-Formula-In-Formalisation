/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Path.Construction

/-!
# Step A: a bounded component exists

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** **Maehara Step A (normalized).** The geometric core in normalized coordinates:
the farthest pair sits at `!₂[-1,0]`, `!₂[1,0]` (so the diameter is `2`). -/
theorem exists_bounded_component_of_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
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
  -- `p 1 < m 1` (else `p = m` would lie in `J_n ∩ J_s = {a,b}` off the axis)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp cfg.topOfSouthernBelow_lt_bottomOfNorthern
  have hz₀1lb : (-2 : ℝ) ≤ z₀ 1 := le_of_lt
    (lt_of_le_of_lt cfg.topOfSouthernBelow_height_mem.1 cfg.topOfSouthernBelow_lt_midpoint)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt
    (lt_of_lt_of_le cfg.midpoint_lt_bottomOfNorthern cfg.bottomOfNorthern_height_mem.2)
  -- `a, b ∉` axis points
  have hmab : m ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.bottomOfNorthern_coord_zero
  have hlab : l ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.topOfNorthern_coord_zero
  have hqab : q ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.bottomOfSouthern_coord_zero
  have hpab : p ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) :=
    not_mem_ends_of_coord_zero cfg.topOfSouthernBelow_coord_zero
  -- **A.0** : `z₀ ∉ range r`
  refine ⟨z₀, cfg.midpoint_not_mem_range, ?_⟩
  -- the rectangle `E`, its open interior `O`
  set E : Set Plane := normalizedRectangle with hEdef
  set O : Set Plane := openNormalizedRectangle with hOdef
  have hEbdd : IsBounded E := isBounded_normalizedRectangle
  have hOopen : IsOpen O := isOpen_openNormalizedRectangle
  have hEclosed : IsClosed E := isClosed_normalizedRectangle
  have hOE : O ⊆ E := openNormalizedRectangle_subset
  have hz₀O : z₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [mem_Ioo, cfg.midpoint_coord_zero]; constructor <;> norm_num
    · rw [mem_Ioo, cfg.midpoint_coord_one]; exact
      ⟨by linarith [cfg.topOfSouthernBelow_height_mem.1,
          cfg.topOfSouthernBelow_lt_bottomOfNorthern],
        by linarith [cfg.bottomOfNorthern_height_mem.2,
          cfg.topOfSouthernBelow_lt_bottomOfNorthern]⟩
  -- assume the component is unbounded and derive a contradiction
  by_contra hUunb
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUeq
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn cfg.midpoint_not_mem_range
  have hUpc : IsPathConnected U := isPathConnected_component r hcont cfg.midpoint_not_mem_range
  have hUnotsub : ¬ U ⊆ E := fun h => hUunb (hEbdd.subset h)
  obtain ⟨y, hyU, hyE⟩ := Set.not_subset.mp hUnotsub
  -- reparametrized escaping path `α : ℝ → Plane`
  have hJoinU : JoinedIn U z₀ y := hUpc.joinedIn z₀ hz₀U y hyU
  set α : ℝ → Plane := fun t => hJoinU.somePath (Set.projIcc (0 : ℝ) 1 (by norm_num) t) with hαdef
  have hαcont : Continuous α := hJoinU.somePath.continuous.comp continuous_projIcc
  have hα0 : α 0 = z₀ := by
    change hJoinU.somePath _ = z₀
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) 0 = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.source
  have hα1 : α 1 = y := by
    change hJoinU.somePath _ = y
    rw [show Set.projIcc (0 : ℝ) 1 (by norm_num) 1 = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.target
  have hαU : ∀ t : ℝ, α t ∈ U := fun t => hJoinU.somePath_mem _
  -- first exit through the frontier `E \ O`
  obtain ⟨tw, htw, hwC, hwO, hbelow⟩ :=
    exists_first_exit_from_rectangle hOopen hEclosed hOE hαcont.continuousOn
      (by rw [hα0]; exact hz₀O)
      (by rw [hα1]; exact hyE)
  have hαE : ∀ u ∈ Icc (0 : ℝ) tw, α u ∈ E := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hwC
    · exact hOE (hbelow u ⟨hu.1, h⟩)
  have hwnr : α tw ∉ range r := hUsub (hαU tw)
  -- `α tw` is off the axis
  have hw1ne : α tw 1 ≠ 0 := by
    intro hzero
    have hnotIoo0 : α tw 0 ∉ Ioo (-1 : ℝ) 1 := fun hIoo =>
      hwO ⟨hIoo, by rw [hzero, mem_Ioo]; constructor <;> norm_num⟩
    rw [mem_Ioo, not_and_or] at hnotIoo0
    rcases hnotIoo0 with h | h
    · have hx : α tw 0 = -1 := le_antisymm (not_lt.mp h) hwC.1.1
      exact hwnr (show α tw ∈ range r from by
        rw [show α tw = normalizedLeftEnd from by ext i; fin_cases i <;> simp [hx, hzero]];
          exact hm)
    · have hx : α tw 0 = 1 := le_antisymm hwC.1.2 (not_lt.mp h)
      exact hwnr (show α tw ∈ range r from by
        rw [show α tw = normalizedRightEnd from by ext i; fin_cases i <;> simp [hx, hzero]];
          exact hp)
  rcases lt_or_gt_of_ne hw1ne with hwneg | hwpos
  · -- **CASE `α tw ∈ Glo`** : build a bottom→top path missing `J_s`
    obtain ⟨Glo, hGloPC, hsGlo, hGloSub, hGloAvoid, hGloFrom⟩ :=
      exists_lower_boundary_path hm hp hfar
    have hwGlo : α tw ∈ Glo := hGloFrom (α tw) hwC.1 hwC.2 hwO hwneg
    -- piece 1 : `s → w` inside `Glo`
    obtain ⟨g1, hg1cont, hg1a, hg1b, hg1mem⟩ :=
      path_reparametrized_on_neg_one_one (hGloPC.joinedIn (axisBottom) hsGlo (α tw) hwGlo)
    -- piece 2 : `w → z₀` along the escaping path
    set g2 : ℝ → Plane := fun t => α (tw * (1 - t) / 2) with hg2def
    have hg2cont : ContinuousOn g2 (Icc (-1 : ℝ) 1) :=
      (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (1 - t) / 2)).continuousOn
    have hg2a : g2 (-1) = α tw := by change α (tw * (1 - (-1)) / 2) = α tw; congr 1; ring
    have hg2b : g2 1 = z₀ := by
      change α (tw * (1 - 1) / 2) = z₀
      rw [show tw * (1 - 1) / 2 = (0 : ℝ) from by ring, hα0]
    have hg2arg : ∀ t ∈ Icc (-1 : ℝ) 1, tw * (1 - t) / 2 ∈ Icc (0 : ℝ) tw := by
      intro t ht; rw [mem_Icc] at ht ⊢
      exact ⟨by nlinarith [htw.1, ht.2], by nlinarith [htw.1, ht.1]⟩
    -- piece 3 : `z₀ → m` along the axis
    set g3 : ℝ → Plane := segmentParam z₀ m with hg3def
    have hg3cont : ContinuousOn g3 (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    have hg3a : g3 (-1) = z₀ := segmentParam_neg1 _ _
    have hg3b : g3 1 = m := segmentParam_one _ _
    have hg3x : ∀ t, g3 t 0 = 0 := fun t => by
      rw [hg3def, segmentParam_coord, cfg.midpoint_coord_zero, hm0]; ring
    have hg3y : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t 1 ∈ Icc (z₀ 1) (m 1) := fun t ht => by
      rw [hg3def]
      exact segmentParam_coord_mem_Icc 1 ⟨le_refl _, cfg.midpoint_lt_bottomOfNorthern.le⟩
        ⟨cfg.midpoint_lt_bottomOfNorthern.le, le_refl _⟩ ht
    have hg3missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_s := by
      intro t ht hJs
      have hy := hg3y t ht; rw [mem_Icc] at hy
      have := hpmax (g3 t) hJs (hg3x t) hy.2
      linarith [hy.1, cfg.topOfSouthernBelow_lt_midpoint]
    -- piece 4 : `m → l` inside `J_n \ {a,b}`
    obtain ⟨g4, hg4cont, hg4a, hg4b, hg4mem⟩ :=
      path_reparametrized_on_neg_one_one (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
    have hg4missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g4 t ∉ J_s := by
      intro t ht hJs
      have hg4 := hg4mem t ht
      have hmem : g4 t ∈ J_n ∩ J_s := ⟨hg4.1, hJs⟩
      rw [hInter] at hmem; exact hg4.2 hmem
    -- piece 5 : `l → n` along the axis
    set g5 : ℝ → Plane := segmentParam l axisTop with hg5def
    have hg5cont : ContinuousOn g5 (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    have hg5a : g5 (-1) = l := segmentParam_neg1 _ _
    have hg5b : g5 1 = axisTop := segmentParam_one _ _
    have hg5x : ∀ t, g5 t 0 = 0 := fun t => by
      rw [hg5def, segmentParam_coord, hl0]; simp
    have hg5y : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t 1 ∈ Icc (l 1) 2 := fun t ht => by
      rw [hg5def]
      exact segmentParam_coord_mem_Icc 1 ⟨le_refl _, cfg.topOfNorthern_height_mem.2⟩
        ⟨by rw [axisTop_coord_one]; exact cfg.topOfNorthern_height_mem.2,
          by rw [axisTop_coord_one]⟩ ht
    have hg5missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t ∉ J_s := by
      intro t ht hJs
      have hy := hg5y t ht; rw [mem_Icc] at hy
      have hle := hlmax (g5 t) (hJsr hJs) (hg5x t)
      have heq : g5 t 1 = l 1 := le_antisymm hle hy.1
      have hgl : g5 t = l := by ext i; fin_cases i <;> simp [hg5x t, hl0, heq]
      rw [hgl] at hJs
      have hmem : l ∈ J_n ∩ J_s := ⟨hlJn, hJs⟩
      rw [hInter] at hmem; exact hlab hmem
    -- concatenate `s → w → z₀ → m → l → n`
    obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
      concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
        (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
    have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact axisBottom_coord_one
    have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact axisTop_coord_one
    have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGloSub (hg1mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg2arg u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg3y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans hz₀1lb hy.1, le_trans hy.2 cfg.bottomOfNorthern_height_mem.2⟩⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hg4mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg5y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg5x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans cfg.topOfNorthern_height_mem.1 hy.1, hy.2⟩⟩
    have hVmiss : ∀ t ∈ Icc (-1 : ℝ) 1, V t ∉ J_s := by
      intro t ht hJs
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
        exact hGloAvoid (g1 u) (hg1mem u hu) (hJsr hJs)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
        exact hUsub (hαU (tw * (1 - u) / 2)) (hJsr hJs)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg3missJs u hu hJs
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg4missJs u hu hJs
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg5missJs u hu hJs
    have hJsrect : J_s ⊆ {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} :=
      fun w hw => hErect (hJsr hw)
    obtain ⟨t, ht, htJs⟩ := vertical_meets_arc hbr hJsrect hJoinJs hVcont hVE hVm1 hVn1
    exact hVmiss t ht htJs
  · -- **CASE `α tw ∈ Gup`** : build a bottom→top path missing `J_n`
    obtain ⟨Gup, hGupPC, hnGup, hGupSub, hGupAvoid, hGupFrom⟩ :=
      exists_upper_boundary_path hm hp hfar
    have hwGup : α tw ∈ Gup := hGupFrom (α tw) hwC.1 hwC.2 hwO hwpos
    -- piece 1 : `s → q` along the axis
    set g1 : ℝ → Plane := segmentParam axisBottom q with hg1def
    have hg1cont : ContinuousOn g1 (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    have hg1a : g1 (-1) = axisBottom := segmentParam_neg1 _ _
    have hg1b : g1 1 = q := segmentParam_one _ _
    have hg1x : ∀ t, g1 t 0 = 0 := fun t => by
      rw [hg1def, segmentParam_coord, axisBottom_coord_zero, hq0]; ring
    have hg1y : ∀ t ∈ Icc (-1 : ℝ) 1, g1 t 1 ∈ Icc (-2 : ℝ) (q 1) := fun t ht => by
      rw [hg1def]
      refine segmentParam_coord_mem_Icc 1 ?_ ⟨cfg.bottomOfSouthern_height_mem.1, le_refl _⟩ ht
      exact ⟨by rw [axisBottom_coord_one],
        by rw [axisBottom_coord_one]; exact cfg.bottomOfSouthern_height_mem.1⟩
    have hg1missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g1 t ∉ J_n := by
      intro t ht hJn
      have hy := hg1y t ht; rw [mem_Icc] at hy
      have := hmmin (g1 t) hJn (hg1x t)
      linarith [hy.2, hqm]
    -- piece 2 : `q → p` inside `J_s \ {a,b}`
    obtain ⟨g2, hg2cont, hg2a, hg2b, hg2mem⟩ :=
      path_reparametrized_on_neg_one_one (hpcJs.joinedIn q ⟨hqJs, hqab⟩ p ⟨hpJs, hpab⟩)
    have hg2missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g2 t ∉ J_n := by
      intro t ht hJn
      have hg2' := hg2mem t ht
      have hmem : g2 t ∈ J_n ∩ J_s := ⟨hJn, hg2'.1⟩
      rw [hInter] at hmem; exact hg2'.2 hmem
    -- piece 3 : `p → z₀` along the axis
    set g3 : ℝ → Plane := segmentParam p z₀ with hg3def
    have hg3cont : ContinuousOn g3 (Icc (-1 : ℝ) 1) :=
      (segmentParam_cont _ _).continuousOn
    have hg3a : g3 (-1) = p := segmentParam_neg1 _ _
    have hg3b : g3 1 = z₀ := segmentParam_one _ _
    have hg3x : ∀ t, g3 t 0 = 0 := fun t => by
      rw [hg3def, segmentParam_coord, hp0, cfg.midpoint_coord_zero]; ring
    have hg3y : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t 1 ∈ Icc (p 1) (z₀ 1) := fun t ht => by
      rw [hg3def]
      exact segmentParam_coord_mem_Icc 1 ⟨le_refl _, cfg.topOfSouthernBelow_lt_midpoint.le⟩
        ⟨cfg.topOfSouthernBelow_lt_midpoint.le, le_refl _⟩ ht
    have hg3missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_n := by
      intro t ht hJn
      have hy := hg3y t ht; rw [mem_Icc] at hy
      have := hmmin (g3 t) hJn (hg3x t)
      linarith [hy.2, cfg.midpoint_lt_bottomOfNorthern]
    -- piece 4 : `z₀ → w` along the escaping path
    set g4 : ℝ → Plane := fun t => α (tw * (t + 1) / 2) with hg4def
    have hg4cont : ContinuousOn g4 (Icc (-1 : ℝ) 1) :=
      (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (t + 1) / 2)).continuousOn
    have hg4a : g4 (-1) = z₀ := by
      change α (tw * ((-1) + 1) / 2) = z₀
      rw [show tw * ((-1) + 1) / 2 = (0 : ℝ) from by ring, hα0]
    have hg4b : g4 1 = α tw := by change α (tw * (1 + 1) / 2) = α tw; congr 1; ring
    have hg4arg : ∀ t ∈ Icc (-1 : ℝ) 1, tw * (t + 1) / 2 ∈ Icc (0 : ℝ) tw := by
      intro t ht; rw [mem_Icc] at ht ⊢
      exact ⟨by nlinarith [htw.1, ht.1], by nlinarith [htw.1, ht.2]⟩
    -- piece 5 : `w → n` inside `Gup`
    obtain ⟨g5, hg5cont, hg5a, hg5b, hg5mem⟩ :=
      path_reparametrized_on_neg_one_one (hGupPC.joinedIn (α tw) hwGup (axisTop) hnGup)
    have hg5missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t ∉ J_n := by
      intro t ht hJn; exact hGupAvoid (g5 t) (hg5mem t ht) (hJnr hJn)
    -- concatenate `s → q → p → z₀ → w → n`
    obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
      concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
        (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
    have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact axisBottom_coord_one
    have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact axisTop_coord_one
    have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg1y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg1x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨hy.1, le_trans hy.2 cfg.bottomOfSouthern_height_mem.2⟩⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hg2mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg3y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans cfg.topOfSouthernBelow_height_mem.1 hy.1, le_trans hy.2 hz₀1ub⟩⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg4arg u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGupSub (hg5mem u hu)
    have hVmiss : ∀ t ∈ Icc (-1 : ℝ) 1, V t ∉ J_n := by
      intro t ht hJn
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg1missJn u hu hJn
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg2missJn u hu hJn
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg3missJn u hu hJn
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn
        exact hUsub (hαU (tw * (u + 1) / 2)) (hJnr hJn)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg5missJn u hu hJn
    have hJnrect : J_n ⊆ {w : Plane | w 0 ∈ Icc (-1 : ℝ) 1 ∧ w 1 ∈ Icc (-2 : ℝ) 2} :=
      fun w hw => hErect (hJnr hw)
    obtain ⟨t, ht, htJn⟩ := vertical_meets_arc hbr hJnrect hJoinJn hVcont hVE hVm1 hVn1
    exact hVmiss t ht htJn

/-- **Math.** **Maehara Step A (geometric core).** The complement `ℝ²∖J` of a Jordan curve
has at least one *bounded* connected component.  Reduced to the normalized version
`exists_bounded_component_of_normalized` via the farthest-pair similarity `T`. -/
theorem exists_bounded_component (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨a, ha, b, hb, hfar, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity_normalizing_farthest_pair hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0 : ℝ) < 2 / dist a b := by positivity
  -- the transported curve `r' = T ∘ r`
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  -- normalized hypotheses for `r'`
  have hm' : normalizedLeftEnd ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : normalizedRightEnd ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b := by
          exact mul_le_mul_of_nonneg_left (hfar z hz w hw) hcpos.le
      _ = 2 := by field_simp
  obtain ⟨x, hx, hxb⟩ := exists_bounded_component_of_normalized hbr hr'cont hr'inj hm' hp' hfar'
  -- transport the bounded component back by `T⁻¹`
  rw [hrange] at hx hxb
  -- `x ∈ (T '' range r)ᶜ = T '' (range r)ᶜ`
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  rw [himg] at hx hxb
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  refine ⟨x₀, hx₀, ?_⟩
  -- component of `x = T x₀` corresponds to component of `x₀` under `T`
  have hcc : connectedComponentIn ((T : Plane → Plane) '' (range r)ᶜ) (T x₀)
      = T '' connectedComponentIn (range r)ᶜ x₀ :=
    (T.image_connectedComponentIn hx₀).symm
  rw [hcc] at hxb
  exact (isBounded_image_scaling hcpos hscale _).mp hxb

end JordanCurve
