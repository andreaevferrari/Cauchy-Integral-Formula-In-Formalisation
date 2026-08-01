/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
module

public import JordanCurve.Path.Concat

/-!
# Maehara's construction points and the boundary paths

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** **The vertical segment `m → s` meets `J_s`.** With `s = !₂[0,-2]` (below the
rectangle's bottom edge), the axis segment from the interior point `m ∈ J_n` down to
`s` must cross the southern arc `J_s`.  Proof by contradiction: were it disjoint from
`J_s`, the concatenation `s → m` (axis), `m → l` (a path inside `J_n \ {a,b}`),
`l → n` (axis, `n = !₂[0,2]`) would give a bottom-to-top path in the rectangle
avoiding `J_s`, contradicting `vertical_meets_arc` (`J_s` joins `a` to `b`).  The
crossing point lies on the segment, so it sits on the axis at height `≤ m 1`. -/
theorem segment_m_to_s_meets_southern_arc (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (_hcont : Continuous r) (_hinj : Injective r)
    (hmr : normalizedLeftEnd ∈ range r) (hpr : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane}
    (hUnion : J_n ∪ J_s = range r)
    (hInter : J_n ∩ J_s = {normalizedLeftEnd, normalizedRightEnd})
    (eJs : ↥J_s ≃ₜ unitInterval)
    (hpcJn : IsPathConnected (J_n \ {normalizedLeftEnd, normalizedRightEnd}))
    {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0)
    (hlmax : ∀ q ∈ range r, q 0 = 0 → q 1 ≤ l 1)
    {m : Plane} (hmJn : m ∈ J_n) (hm0 : m 0 = 0) :
    ∃ w ∈ J_s, w 0 = 0 ∧ w 1 ≤ m 1 := by
  set a : Plane := normalizedLeftEnd with ha_def
  set b : Plane := normalizedRightEnd with hb_def
  -- opaque bottom / top axis points (avoid unfolding `!₂` in later arithmetic)
  obtain ⟨s, hs0, hs1⟩ : ∃ s : Plane, s 0 = 0 ∧ s 1 = -2 :=
    ⟨axisBottom, by simp, by simp⟩
  obtain ⟨nn, hn0, hn1⟩ : ∃ nn : Plane, nn 0 = 0 ∧ nn 1 = 2 :=
    ⟨axisTop, by simp, by simp⟩
  have ha0 : a 0 = -1 := by simp [ha_def]
  have hb0 : b 0 = 1 := by simp [hb_def]
  -- basic containments and the rectangle bound
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hrect := normalized_subset_rectangle hmr hpr hfar
  have hmrange : m ∈ range r := hJnr hmJn
  have hlrange : l ∈ range r := hJnr hlJn
  have hm1lb : (-2 : ℝ) ≤ m 1 := (hrect hmrange).2.1
  have hm1ub : m 1 ≤ 2 := (hrect hmrange).2.2
  have hl1lb : (-2 : ℝ) ≤ l 1 := (hrect hlrange).2.1
  have hl1ub : l 1 ≤ 2 := (hrect hlrange).2.2
  -- `a, b ∈ J_s`; `J_s` joins them
  have haJs : a ∈ J_s := by
    have : a ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert _ _
    exact this.2
  have hbJs : b ∈ J_s := by
    have : b ∈ J_n ∩ J_s := by rw [hInter]; exact Set.mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJs : JoinedIn J_s a b := arc_joinedIn eJs haJs hbJs
  have hJsrect : J_s ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} :=
    hJsr.trans hrect
  -- `m, l ∉ {a,b}` (they are on the axis `x = 0`, while `a 0 = -1`, `b 0 = 1`)
  have hmab : m ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hm0, ha0, hb0] at hc; norm_num at hc)
  have hlab : l ∉ ({a, b} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun p : Plane => p 0) h;
       simp only [hl0, ha0, hb0] at hc; norm_num at hc)
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ w ∈ J_s, w 0 = 0 → m 1 < w 1`
  -- three path pieces on `[-1,1]`
  set f1 : ℝ → Plane := fun t => s + ((t + 1) / 2) • (m - s) with hf1def
  set f3 : ℝ → Plane := fun t => l + ((t + 1) / 2) • (nn - l) with hf3def
  obtain ⟨f2, hf2cont, hf2m, hf2l, hf2mem⟩ :=
    path_reparametrized_on_neg_one_one (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hf1cont : ContinuousOn f1 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous f1).continuousOn
  have hf3cont : ContinuousOn f3 (Icc (-1 : ℝ) 1) := (by fun_prop : Continuous f3).continuousOn
  have hf1_1 : f1 1 = m := by simp [hf1def]
  have hf1_m1 : f1 (-1) = s := by simp [hf1def]
  have hf3_1 : f3 1 = nn := by simp [hf3def]
  have hf3_m1 : f3 (-1) = l := by simp [hf3def]
  have hf1f2 : f1 1 = f2 (-1) := by rw [hf1_1, hf2m]
  have hf2f3 : f2 1 = f3 (-1) := by rw [hf2l, hf3_m1]
  obtain ⟨c, hccont, hcs, hcn, hcmem⟩ := concatPath3 hf1cont hf2cont hf3cont hf1f2 hf2f3
  -- endpoints of the concatenation are on the bottom / top edges
  have hcm1 : c (-1) 1 = -2 := by rw [hcs, hf1_m1]; exact hs1
  have hcn1 : c 1 1 = 2 := by rw [hcn, hf3_1]; exact hn1
  -- the three pieces stay in the rectangle
  have hf1x : ∀ t, f1 t 0 = 0 := fun t => by simp [hf1def, hs0, hm0]
  have hf3x : ∀ t, f3 t 0 = 0 := fun t => by simp [hf3def, hl0, hn0]
  have hf1y_le : ∀ t ∈ Icc (-1 : ℝ) 1, f1 t 1 ≤ m 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf1y_ge : ∀ t ∈ Icc (-1 : ℝ) 1, (-2 : ℝ) ≤ f1 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf1def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hs1]
    nlinarith [ht.1, ht.2, hm1lb]
  have hf3y_ge : ∀ t ∈ Icc (-1 : ℝ) 1, l 1 ≤ f3 t 1 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1ub]
  have hf3y_le : ∀ t ∈ Icc (-1 : ℝ) 1, f3 t 1 ≤ 2 := by
    intro t ht; rw [mem_Icc] at ht
    simp only [hf3def, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hn1]
    nlinarith [ht.1, ht.2, hl1lb, hl1ub]
  have hbound : ∀ z ∈ (f1 '' Icc (-1 : ℝ) 1 ∪ f2 '' Icc (-1 : ℝ) 1) ∪ f3 '' Icc (-1 : ℝ) 1,
      z 0 ∈ Icc (-1 : ℝ) 1 ∧ z 1 ∈ Icc (-2 : ℝ) 2 := by
    rintro z ((⟨t1, ht1, rfl⟩ | ⟨t2, ht2, rfl⟩) | ⟨t3, ht3, rfl⟩)
    · exact ⟨by rw [hf1x]; norm_num,
        mem_Icc.2 ⟨hf1y_ge t1 ht1, le_trans (hf1y_le t1 ht1) hm1ub⟩⟩
    · exact hrect (hJnr (hf2mem t2 ht2).1)
    · exact ⟨by rw [hf3x]; norm_num,
        mem_Icc.2 ⟨le_trans hl1lb (hf3y_ge t3 ht3), hf3y_le t3 ht3⟩⟩
  have hcE : ∀ t ∈ Icc (-1 : ℝ) 1, c t 0 ∈ Icc (-1 : ℝ) 1 ∧ c t 1 ∈ Icc (-2 : ℝ) 2 :=
    fun t ht => hbound (c t) (hcmem t ht)
  -- the concatenation is a bottom-to-top path, so it must meet `J_s`
  obtain ⟨t, ht, hctJs⟩ :=
    vertical_meets_arc hbr hJsrect hJoinJs hccont hcE hcm1 hcn1
  rcases hcmem t ht with (⟨t1, ht1, ht1e⟩ | ⟨t2, ht2, ht2e⟩) | ⟨t3, ht3, ht3e⟩
  · -- on the lower axis segment: contradicts `hcon` (height `≤ m 1`)
    have hct0 : c t 0 = 0 := by rw [← ht1e]; exact hf1x t1
    have hcty : c t 1 ≤ m 1 := by rw [← ht1e]; exact hf1y_le t1 ht1
    exact absurd (hcon (c t) hctJs hct0) (not_lt.2 hcty)
  · -- on the middle piece: lands in `J_n \ {a,b}`, disjoint from `J_s`
    have hctJn : c t ∈ J_n := ht2e ▸ (hf2mem t2 ht2).1
    have hctnab : c t ∉ ({a, b} : Set Plane) := ht2e ▸ (hf2mem t2 ht2).2
    have : c t ∈ J_n ∩ J_s := ⟨hctJn, hctJs⟩
    rw [hInter] at this
    exact hctnab this
  · -- on the upper axis segment: forced to equal `l`, but `l ∉ J_s`
    have hct0 : c t 0 = 0 := by rw [← ht3e]; exact hf3x t3
    have hcty_ge : l 1 ≤ c t 1 := by rw [← ht3e]; exact hf3y_ge t3 ht3
    have hcty_le : c t 1 ≤ l 1 := hlmax (c t) (hJsr hctJs) hct0
    have hcty : c t 1 = l 1 := le_antisymm hcty_le hcty_ge
    have hctl : c t = l := by ext i; fin_cases i <;> simp [hct0, hl0, hcty]
    have hlnJs : l ∉ J_s := by
      intro h
      have : l ∈ J_n ∩ J_s := ⟨hlJn, h⟩
      rw [hInter] at this; exact hlab this
    exact hlnJs (hctl ▸ hctJs)

/-- **Maehara's construction points.** Bundles the five points of Maehara's figure
on the vertical axis `x = 0`:
* `l` — the topmost intersection of the axis with the curve (in `J_n`);
* `m` — the lowest point of `J_n` on the axis;
* `p` — the highest point of `J_s` on the axis lying at or below `m` (the top of the
  southern arc on the segment `m → s`, via `segment_m_to_s_meets_southern_arc`);
* `q` — the lowest point of `J_s` on the axis;
* `z₀` — the midpoint `!₂[0,(m 1 + p 1)/2]` of `m` and `p`.

The established `y`-ordering is `q 1 ≤ p 1 ≤ z₀ 1 ≤ m 1 ≤ l 1`.  (Note `p` is the
`J_s`-max **restricted to heights `≤ m 1`**; this is what makes `p 1 ≤ m 1` — hence
the placement of `z₀` between `p` and `m` — provable at this stage.) -/
theorem exists_maehara_configuration (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    Nonempty (MaeharaConfiguration r) := by
  obtain ⟨J_n, J_s, hJncl, hJscl, hUnion, hInter, ⟨eJn⟩, ⟨eJs⟩, hpcJn, hpcJs,
    l, hlr, hl0, hlmax, hlJn⟩ := exists_arc_decomposition_of_curve hbr hcont hinj hm hp hfar
  have hcptr : IsCompact (range r) := jordanCurve_isCompact r hcont
  have hJnr : J_n ⊆ range r := by rw [← hUnion]; exact subset_union_left
  have hJsr : J_s ⊆ range r := by rw [← hUnion]; exact subset_union_right
  have hJncpt : IsCompact J_n := hcptr.of_isClosed_subset hJncl hJnr
  have hJscpt : IsCompact J_s := hcptr.of_isClosed_subset hJscl hJsr
  -- `m` : lowest point of `J_n` on the axis
  obtain ⟨m, hmJn, hm0, hmmin⟩ := exists_lowest_point_of_northern_arc_on_axis hJncl hJncpt hlJn hl0
  -- `J_s` meets the axis below `m`
  obtain ⟨w₀, hw₀Js, hw₀0, hw₀m⟩ :=
    segment_m_to_s_meets_southern_arc hbr hcont hinj hm hp hfar hUnion hInter eJs
      hpcJn hlJn hl0 hlmax hmJn hm0
  -- `p` : highest point of `J_s` on the axis at or below `m`
  set Sp : Set Plane := {w ∈ J_s | w 0 = 0 ∧ w 1 ≤ m 1} with hSpdef
  have hSpcl : IsClosed Sp := by
    have hEq : Sp = (J_s ∩ {w : Plane | w 0 = 0}) ∩ {w : Plane | w 1 ≤ m 1} := by
      ext w
      constructor
      · rintro ⟨hJ, h0, hle⟩; exact ⟨⟨hJ, h0⟩, hle⟩
      · rintro ⟨⟨hJ, h0⟩, hle⟩; exact ⟨hJ, h0, hle⟩
    rw [hEq]
    exact (hJscl.inter (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hSpcpt : IsCompact Sp := hJscpt.of_isClosed_subset hSpcl (fun w hw => hw.1)
  obtain ⟨p, hpSp, hpmax⟩ := hSpcpt.exists_isMaxOn ⟨w₀, hw₀Js, hw₀0, hw₀m⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- `q` : lowest point of `J_s` on the axis
  set Sq : Set Plane := {w ∈ J_s | w 0 = 0} with hSqdef
  have hSqcl : IsClosed Sq :=
    hJscl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hSqcpt : IsCompact Sq := hJscpt.of_isClosed_subset hSqcl (fun w hw => hw.1)
  obtain ⟨q, hqSq, hqmin⟩ := hSqcpt.exists_isMinOn ⟨w₀, hw₀Js, hw₀0⟩
    (f := fun w : Plane => w 1) (by fun_prop : Continuous (fun w : Plane => w 1)).continuousOn
  -- extract the packaged facts
  have hpm : p 1 ≤ m 1 := hpSp.2.2
  have hml : m 1 ≤ l 1 := hlmax m (hJnr hmJn) hm0
  have hqp : q 1 ≤ p 1 := hqmin ⟨hpSp.1, hpSp.2.1⟩
  have haJn : normalizedLeftEnd ∈ J_n := by
    have : normalizedLeftEnd ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.1
  have hbJn : normalizedRightEnd ∈ J_n := by
    have : normalizedRightEnd ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.1
  have haJs : normalizedLeftEnd ∈ J_s := by
    have : normalizedLeftEnd ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert _ _
    exact this.2
  have hbJs : normalizedRightEnd ∈ J_s := by
    have : normalizedRightEnd ∈ J_n ∩ J_s := by rw [hInter]; exact mem_insert_of_mem _ rfl
    exact this.2
  have hJoinJn : JoinedIn J_n (normalizedLeftEnd) (normalizedRightEnd) := arc_joinedIn eJn haJn hbJn
  have hJoinJs : JoinedIn J_s (normalizedLeftEnd) (normalizedRightEnd) := arc_joinedIn eJs haJs hbJs
  refine ⟨{ northern := J_n, southern := J_s
            topOfNorthern := l, bottomOfNorthern := m
            topOfSouthernBelow := p, bottomOfSouthern := q
            midpoint := !₂[(0 : ℝ), (m 1 + p 1) / 2]
            subset_rectangle := normalized_subset_rectangle hm hp hfar
            union_eq := hUnion, inter_eq := hInter
            isPathConnected_northern := hpcJn, isPathConnected_southern := hpcJs
            joinedIn_northern := hJoinJn, joinedIn_southern := hJoinJs
            topOfNorthern_mem := hlJn, topOfNorthern_coord_zero := hl0
            topOfNorthern_max := hlmax
            bottomOfNorthern_mem := hmJn, bottomOfNorthern_coord_zero := hm0
            bottomOfNorthern_min := hmmin
            topOfSouthernBelow_mem := hpSp.1
            topOfSouthernBelow_coord_zero := hpSp.2.1
            topOfSouthernBelow_le := hpm
            topOfSouthernBelow_max := fun w hwJs hw0 hwm => hpmax ⟨hwJs, hw0, hwm⟩
            bottomOfSouthern_mem := hqSq.1, bottomOfSouthern_coord_zero := hqSq.2
            bottomOfSouthern_min := fun w hwJs hw0 => hqmin ⟨hwJs, hw0⟩
            midpoint_eq := rfl
            bottomOfNorthern_le_topOfNorthern := hml
            bottomOfSouthern_le_topOfSouthernBelow := hqp
            topOfSouthernBelow_le_midpoint := ?_
            midpoint_le_bottomOfNorthern := ?_ }⟩
  · rw [show (!₂[(0 : ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]
  · rw [show (!₂[(0 : ℝ), (m 1 + p 1) / 2] : Plane) 1 = (m 1 + p 1) / 2 from by simp]
    linarith [hpm]

/-- **Math.** **First-exit lemma (A.1).** A path `α` on `[0,1]` starting inside an open set `O`
and ending outside a closed superset `C ⊇ O` has a *first exit time* `tw ∈ (0,1]`:
`α tw` lies in the frontier layer `C \ O`, and `α u ∈ O` for all `u < tw`. -/
theorem exists_first_exit_from_rectangle {α : ℝ → Plane} {O C : Set Plane}
    (hO : IsOpen O) (hC : IsClosed C) (hOC : O ⊆ C)
    (hcont : ContinuousOn α (Icc (0 : ℝ) 1))
    (h0 : α 0 ∈ O) (h1 : α 1 ∉ C) :
    ∃ tw ∈ Ioc (0 : ℝ) 1, α tw ∈ C ∧ α tw ∉ O ∧ ∀ u ∈ Ico (0 : ℝ) tw, α u ∈ O := by
  set S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | α t ∉ O} with hSdef
  -- `S` is closed: it is `Icc 0 1 ∩ α⁻¹(Oᶜ)`
  have hScl : IsClosed S := by
    have hEq : S = Icc (0 : ℝ) 1 ∩ α ⁻¹' Oᶜ := by
      ext t; simp only [hSdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    rw [hEq]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty :=
    ⟨1, ⟨by norm_num, fun h => h1 (hOC h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set tw := sInf S with htw
  have htwS : tw ∈ S := hScl.csInf_mem hSne hSbdd
  have htw01 : tw ∈ Icc (0 : ℝ) 1 := htwS.1
  have htwO : α tw ∉ O := htwS.2
  -- `tw > 0` (since `0 ∉ S`)
  have h0S : (0 : ℝ) ∉ S := fun h => h.2 h0
  have htwpos : 0 < tw := lt_of_le_of_ne htw01.1 (fun h => h0S (h ▸ htwS))
  -- points strictly below `tw` are still in `O`
  have hbelow : ∀ u ∈ Ico (0 : ℝ) tw, α u ∈ O := by
    intro u hu
    by_contra hnot
    have huS : u ∈ S := ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hnot⟩
    exact absurd (csInf_le hSbdd huS) (not_le.2 hu.2)
  -- `α tw ∈ C` by closure of the pre-exit segment
  have htwC : α tw ∈ C := by
    have hT : IsClosed (Icc (0 : ℝ) 1 ∩ α ⁻¹' C) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hsub : Ico (0 : ℝ) tw ⊆ Icc (0 : ℝ) 1 ∩ α ⁻¹' C := by
      intro u hu
      exact ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hOC (hbelow u hu)⟩
    have : tw ∈ Icc (0 : ℝ) 1 ∩ α ⁻¹' C := by
      apply hT.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt htwpos)]
      exact ⟨htwpos.le, le_refl tw⟩
    exact this.2
  exact ⟨tw, ⟨htwpos, htw01.2⟩, htwC, htwO, hbelow⟩

/-- **Math.** A vertical segment `{p | p 0 = c ∧ p 1 ∈ T}` (with `T` path-connected) is
path-connected: it is the image of `T` under `y ↦ !₂[c, y]`. -/
theorem isPathConnected_verticalSegment (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
  have hfcont : Continuous (fun y : ℝ => (!₂[c, y] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun y : ℝ => (!₂[c, y] : Plane)) '' T = {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
    ext p
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 1, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- **Math.** A horizontal segment `{p | p 1 = c ∧ p 0 ∈ T}` is path-connected. -/
theorem isPathConnected_horizontalSegment (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
  have hfcont : Continuous (fun x : ℝ => (!₂[x, c] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun x : ℝ => (!₂[x, c] : Plane)) '' T = {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
    ext p
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 0, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- **Math.** **Curve meets the rectangle boundary only on the axis (A.2).** Any curve point on
the frontier of the normalized rectangle `[-1,1]×[-2,2]` has `y = 0` (so it is `a` or
`b`).  The "lens" bound `(p 0±1)²+(p 1)² ≤ 4` rules out the top/bottom edges outright
and pins the left/right edges to `y = 0`. -/
theorem curve_meets_axis_within_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ p ∈ range r, (p 0 = -1 ∨ p 0 = 1 ∨ p 1 = -2 ∨ p 1 = 2) → p 1 = 0 := by
  intro p hp' hbdry
  have hza : dist p (normalizedLeftEnd) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hm; nlinarith [dist_nonneg (x := p) (y := normalizedLeftEnd)]
  have hzb : dist p (normalizedRightEnd) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hp; nlinarith [dist_nonneg (x := p) (y := normalizedRightEnd)]
  rw [dist_sq_eq_sum_coord_sq] at hza hzb
  simp only [normalizedLeftEnd_coord_zero, normalizedLeftEnd_coord_one,
    normalizedRightEnd_coord_zero, normalizedRightEnd_coord_one] at hza hzb
  rcases hbdry with h | h | h | h
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hzb]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hza]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 + 2)]
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 - 2)]

/-- **Math.** **Lower boundary arc (A.2).** The part of the rectangle frontier with `y < 0` is
path-connected, contains the bottom axis point `!₂[0,-2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y < 0` lies in it. -/
theorem exists_lower_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      axisBottom ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1 : ℝ) 1 → p 1 ∈ Icc (-2 : ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2) → p 1 < 0 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ico (-2 : ℝ) 0} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ico (-2 : ℝ) 0} with hRdef
  set Bot : Set Plane := {p : Plane | p 1 = -2 ∧ p 0 ∈ Icc (-1 : ℝ) 1} with hBdef
  have hLpc : IsPathConnected L :=
    isPathConnected_verticalSegment (-1)
      ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_verticalSegment 1
      ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hBpc : IsPathConnected Bot :=
    isPathConnected_horizontalSegment (-2)
      ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1 : ℝ), -2] : Plane) ∈ L :=
    ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have memBotL : (!₂[(-1 : ℝ), -2] : Plane) ∈ Bot :=
    ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memBotR : (!₂[(1 : ℝ), -2] : Plane) ∈ Bot :=
    ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1 : ℝ), -2] : Plane) ∈ Rt :=
    ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have hLB : IsPathConnected (L ∪ Bot) := hLpc.union hBpc ⟨_, memL, memBotL⟩
  have hG : IsPathConnected ((L ∪ Bot) ∪ Rt) := hLB.union hRpc ⟨_, Or.inr memBotR, memR⟩
  refine ⟨(L ∪ Bot) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.2]
    · have := curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inr (Or.inr (Or.inl hpp.1)))
      linarith [hpp.1]
    · have :=
      curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.2]
  · intro p hp0 hp1 hnint hpneg
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exact Or.inl (Or.inr ⟨le_antisymm (not_lt.mp h) hp1.1, hp0⟩)
      · exfalso; linarith [not_lt.mp h]

/-- **Math.** **Upper boundary arc (A.2).** The part of the rectangle frontier with `y > 0` is
path-connected, contains the top axis point `!₂[0,2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y > 0` lies in it. -/
theorem exists_upper_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      axisTop ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 ∈ Icc (-2 : ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1 : ℝ) 1 → p 1 ∈ Icc (-2 : ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1 : ℝ) 1 ∧ p 1 ∈ Ioo (-2 : ℝ) 2) → 0 < p 1 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ioc (0 : ℝ) 2} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ioc (0 : ℝ) 2} with hRdef
  set Top : Set Plane := {p : Plane | p 1 = 2 ∧ p 0 ∈ Icc (-1 : ℝ) 1} with hTdef
  have hLpc : IsPathConnected L :=
    isPathConnected_verticalSegment (-1)
      ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_verticalSegment 1
      ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hTpc : IsPathConnected Top :=
    isPathConnected_horizontalSegment 2
      ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1 : ℝ), 2] : Plane) ∈ L :=
    ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have memTopL : (!₂[(-1 : ℝ), 2] : Plane) ∈ Top :=
    ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memTopR : (!₂[(1 : ℝ), 2] : Plane) ∈ Top :=
    ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1 : ℝ), 2] : Plane) ∈ Rt :=
    ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have hLT : IsPathConnected (L ∪ Top) := hLpc.union hTpc ⟨_, memL, memTopL⟩
  have hG : IsPathConnected ((L ∪ Top) ∪ Rt) := hLT.union hRpc ⟨_, Or.inr memTopR, memR⟩
  refine ⟨(L ∪ Top) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.1]
    · have := curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inr (Or.inr (Or.inr hpp.1)))
      linarith [hpp.1]
    · have :=
      curve_meets_axis_within_rectangle hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.1]
  · intro p hp0 hp1 hnint hppos
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exfalso; linarith [not_lt.mp h]
      · exact Or.inl (Or.inr ⟨le_antisymm hp1.2 (not_lt.mp h), hp0⟩)


end JordanCurve
