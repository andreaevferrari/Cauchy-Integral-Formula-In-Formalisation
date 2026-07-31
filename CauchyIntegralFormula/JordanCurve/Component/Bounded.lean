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

set_option maxHeartbeats 1600000 in
-- A 325-line proof: the elaborator needs more than the default budget to get
-- through it. Inherited from the original development, and a standing reason
-- to break the proof up rather than to keep the option.
/-- **Math.** **Maehara Step A (normalized).** The geometric core in normalized coordinates:
the farthest pair sits at `!₂[-1,0]`, `!₂[1,0]` (so the diameter is `2`). -/
theorem exists_bounded_component_of_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1 : ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_maehara_points_on_axis hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have ha0 : (!₂[(-1 : ℝ), 0] : Plane) 0 = -1 := by simp
  have hb0 : (!₂[(1 : ℝ), 0] : Plane) 0 = 1 := by simp
  have hs0 : (!₂[(0 : ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0 : ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0 : ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0 : ℝ), 2] : Plane) 1 = 2 := by simp
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmE1 : m 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hmJn)).2
  have hlE1 : l 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJnr hlJn)).2
  have hpE1 : p 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hpJs)).2
  have hqE1 : q 1 ∈ Icc (-2 : ℝ) 2 := (hErect (hJsr hqJs)).2
  -- `p 1 < m 1` (else `p = m` would lie in `J_n ∩ J_s = {a,b}` off the axis)
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  have hz₀1lb : (-2 : ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  -- `a, b ∉` axis points
  have hmab : m ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hm0] at hc; norm_num at hc)
  have hlab : l ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hl0] at hc; norm_num at hc)
  have hqab : q ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hq0] at hc; norm_num at hc)
  have hpab : p ∉ ({!₂[(-1 : ℝ), 0], !₂[(1 : ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hp0] at hc; norm_num at hc)
  -- **A.0** : `z₀ ∉ range r`
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  refine ⟨z₀, hz₀c, ?_⟩
  -- the rectangle `E`, its open interior `O`
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} with hEdef
  set O : Set Plane := {p : Plane | p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2} with hOdef
  have hEbdd : IsBounded E := by
    apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 3)).subset
    intro z hz
    rw [Metric.mem_closedBall]
    have hz1 := hz.1; have hz2 := hz.2; rw [mem_Icc] at hz1 hz2
    have hsq : dist z (0:Plane) ^ 2 ≤ 9 := by
      rw [dist_sq_eq_sum_coord_sq, show (0:Plane) 0 = 0 from by simp,
        show (0:Plane) 1 = 0 from by simp]
      nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
    nlinarith [dist_nonneg (x := z) (y := (0:Plane)), hsq]
  have hproj0 : Continuous (fun w : Plane => w 0) := by fun_prop
  have hproj1 : Continuous (fun w : Plane => w 1) := by fun_prop
  have hOopen : IsOpen O := by
    have hEq : O = (fun w : Plane => w 0) ⁻¹' Ioo (-1 : ℝ) 1
        ∩ (fun w : Plane => w 1) ⁻¹' Ioo (-2 : ℝ) 2 := by
      ext w; simp only [hOdef, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [hEq]; exact (isOpen_Ioo.preimage hproj0).inter (isOpen_Ioo.preimage hproj1)
  have hEclosed : IsClosed E := by
    have hEq : E = (fun w : Plane => w 0) ⁻¹' Icc (-1 : ℝ) 1
        ∩ (fun w : Plane => w 1) ⁻¹' Icc (-2 : ℝ) 2 := by
      ext w; simp only [hEdef, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [hEq]; exact (isClosed_Icc.preimage hproj0).inter (isClosed_Icc.preimage hproj1)
  have hOE : O ⊆ E := fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hz₀O : z₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [mem_Ioo, hz₀0]; constructor <;> norm_num
    · rw [mem_Ioo, hz₀1e]; exact ⟨by linarith [hpE1.1, hpm_lt], by linarith [hmE1.2, hpm_lt]⟩
  -- assume the component is unbounded and derive a contradiction
  by_contra hUunb
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUeq
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  have hUpc : IsPathConnected U := isPathConnected_component r hcont hz₀c
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
        rw [show α tw = !₂[(-1 : ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hzero]]; exact hm)
    · have hx : α tw 0 = 1 := le_antisymm hwC.1.2 (not_lt.mp h)
      exact hwnr (show α tw ∈ range r from by
        rw [show α tw = !₂[(1 : ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hzero]]; exact hp)
  rcases lt_or_gt_of_ne hw1ne with hwneg | hwpos
  · -- **CASE `α tw ∈ Glo`** : build a bottom→top path missing `J_s`
    obtain ⟨Glo, hGloPC, hsGlo, hGloSub, hGloAvoid, hGloFrom⟩ :=
      exists_lower_boundary_path hm hp hfar
    have hwGlo : α tw ∈ Glo := hGloFrom (α tw) hwC.1 hwC.2 hwO hwneg
    -- piece 1 : `s → w` inside `Glo`
    obtain ⟨g1, hg1cont, hg1a, hg1b, hg1mem⟩ :=
      path_reparametrized_on_neg_one_one (hGloPC.joinedIn (!₂[(0 : ℝ), -2]) hsGlo (α tw) hwGlo)
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
    set g3 : ℝ → Plane := fun t => z₀ + ((t + 1) / 2) • (m - z₀) with hg3def
    have hg3cont : ContinuousOn g3 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous g3).continuousOn
    have hg3a : g3 (-1) = z₀ := by simp [hg3def]
    have hg3b : g3 1 = m := by simp [hg3def]
    have hg3x : ∀ t, g3 t 0 = 0 := fun t => by simp [hg3def, hz₀0, hm0]
    have hg3y : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t 1 ∈ Icc (z₀ 1) (m 1) := by
      intro t ht; rw [mem_Icc] at ht ⊢
      simp only [hg3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      constructor <;> nlinarith [ht.1, ht.2, hz₀m_lt.le]
    have hg3missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_s := by
      intro t ht hJs
      have hy := hg3y t ht; rw [mem_Icc] at hy
      have := hpmax (g3 t) hJs (hg3x t) hy.2
      linarith [hy.1, hpz₀_lt]
    -- piece 4 : `m → l` inside `J_n \ {a,b}`
    obtain ⟨g4, hg4cont, hg4a, hg4b, hg4mem⟩ :=
      path_reparametrized_on_neg_one_one (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
    have hg4missJs : ∀ t ∈ Icc (-1 : ℝ) 1, g4 t ∉ J_s := by
      intro t ht hJs
      have hg4 := hg4mem t ht
      have hmem : g4 t ∈ J_n ∩ J_s := ⟨hg4.1, hJs⟩
      rw [hInter] at hmem; exact hg4.2 hmem
    -- piece 5 : `l → n` along the axis
    set g5 : ℝ → Plane := fun t => l + ((t + 1) / 2) • ((!₂[(0 : ℝ), 2] : Plane) - l) with hg5def
    have hg5cont : ContinuousOn g5 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous g5).continuousOn
    have hg5a : g5 (-1) = l := by simp [hg5def]
    have hg5b : g5 1 = !₂[(0 : ℝ), 2] := by simp [hg5def]
    have hg5x : ∀ t, g5 t 0 = 0 := fun t => by simp [hg5def, hl0]
    have hg5y : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t 1 ∈ Icc (l 1) 2 := by
      intro t ht; rw [mem_Icc] at ht ⊢
      simp only [hg5def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      constructor <;> nlinarith [ht.1, ht.2, hlE1.2]
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
    have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
    have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
    have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGloSub (hg1mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg2arg u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg3y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans hz₀1lb hy.1, le_trans hy.2 hmE1.2⟩⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hg4mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg5y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg5x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans hlE1.1 hy.1, hy.2⟩⟩
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
    set g1 : ℝ → Plane :=
      fun t => (!₂[(0 : ℝ), -2] : Plane) + ((t + 1) / 2) • (q - (!₂[(0 : ℝ), -2] : Plane))
      with hg1def
    have hg1cont : ContinuousOn g1 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous g1).continuousOn
    have hg1a : g1 (-1) = !₂[(0 : ℝ), -2] := by simp [hg1def]
    have hg1b : g1 1 = q := by simp [hg1def]
    have hg1x : ∀ t, g1 t 0 = 0 := fun t => by simp [hg1def, hq0]
    have hg1y : ∀ t ∈ Icc (-1 : ℝ) 1, g1 t 1 ∈ Icc (-2 : ℝ) (q 1) := by
      intro t ht; rw [mem_Icc] at ht ⊢
      simp only [hg1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      constructor <;> nlinarith [ht.1, ht.2, hqE1.1]
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
    set g3 : ℝ → Plane := fun t => p + ((t + 1) / 2) • (z₀ - p) with hg3def
    have hg3cont : ContinuousOn g3 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous g3).continuousOn
    have hg3a : g3 (-1) = p := by simp [hg3def]
    have hg3b : g3 1 = z₀ := by simp [hg3def]
    have hg3x : ∀ t, g3 t 0 = 0 := fun t => by simp [hg3def, hp0, hz₀0]
    have hg3y : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t 1 ∈ Icc (p 1) (z₀ 1) := by
      intro t ht; rw [mem_Icc] at ht ⊢
      simp only [hg3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      constructor <;> nlinarith [ht.1, ht.2, hpz₀_lt.le]
    have hg3missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g3 t ∉ J_n := by
      intro t ht hJn
      have hy := hg3y t ht; rw [mem_Icc] at hy
      have := hmmin (g3 t) hJn (hg3x t)
      linarith [hy.2, hz₀m_lt]
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
      path_reparametrized_on_neg_one_one (hGupPC.joinedIn (α tw) hwGup (!₂[(0 : ℝ), 2]) hnGup)
    have hg5missJn : ∀ t ∈ Icc (-1 : ℝ) 1, g5 t ∉ J_n := by
      intro t ht hJn; exact hGupAvoid (g5 t) (hg5mem t ht) (hJnr hJn)
    -- concatenate `s → q → p → z₀ → w → n`
    obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
      concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
        (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
    have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
    have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
    have hVE : ∀ t ∈ Icc (-1 : ℝ) 1, V t 0 ∈ Icc (-1 : ℝ) 1 ∧ V t 1 ∈ Icc (-2 : ℝ) 2 := by
      intro t ht
      rcases hVmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg1y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg1x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨hy.1, le_trans hy.2 hqE1.2⟩⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hg2mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        have hy := hg3y u hu; rw [mem_Icc] at hy
        exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
          mem_Icc.2 ⟨le_trans hpE1.1 hy.1, le_trans hy.2 hz₀1ub⟩⟩
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
  have hm' : (!₂[(-1 : ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1 : ℝ), 0] : Plane) ∈ range r' := by
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
