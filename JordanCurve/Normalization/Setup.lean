/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import JordanCurve.Normalization.Configuration

/-!
# Setup lemmas in the normalized frame

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-! ### Setup lemmas for the normalized frame (Steps A, B) -/

/-- **Math.** Squared Euclidean distance in `Plane` expanded in coordinates. -/
lemma dist_sq_eq_sum_coord_sq (z w : Plane) :
    dist z w ^ 2 = (z 0 - w 0) ^ 2 + (z 1 - w 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **Math.** **Setup 1 (the "lens").** In the normalized frame with the farthest pair at
`a = !₂[-1,0]`, `b = !₂[1,0]` and diameter `2` (`hfar`), the whole curve lies in
the rectangle `[-1,1] × [-2,2]`.  For `z ∈ range r`, both `dist z a ≤ 2` and
`dist z b ≤ 2`, i.e. `(z 0+1)²+(z 1)² ≤ 4` and `(z 0-1)²+(z 1)² ≤ 4`; these force
`z 0 ∈ [-1,1]` and (adding them) `(z 0)²+(z 1)² ≤ 3`, hence `z 1 ∈ [-2,2]`. -/
theorem normalized_subset_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    range r ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} := by
  intro z hz
  have hza : dist z (normalizedLeftEnd) ≤ 2 := hfar z hz _ hm
  have hzb : dist z (normalizedRightEnd) ≤ 2 := hfar z hz _ hp
  have hza2 : dist z (normalizedLeftEnd) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := normalizedLeftEnd)]
  have hzb2 : dist z (normalizedRightEnd) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := normalizedRightEnd)]
  rw [dist_sq_eq_sum_coord_sq] at hza2 hzb2
  have ea0 : normalizedLeftEnd 0 = -1 := by simp
  have ea1 : normalizedLeftEnd 1 = 0 := by simp
  have eb0 : normalizedRightEnd 0 = 1 := by simp
  have eb1 : normalizedRightEnd 1 = 0 := by simp
  rw [ea0, ea1] at hza2
  rw [eb0, eb1] at hzb2
  simp only [mem_setOf_eq, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]

/-- **Math.** **`path_reparametrized_on_neg_one_one`** (reusable
reparametrization). A path in a set `S ⊆ Plane`
joining `a` to `b` can be reparametrized to a map `h : ℝ → Plane` on the interval
`[-1,1]`, with `h (-1) = a`, `h 1 = b`, continuous on `[-1,1]`, and staying in `S`.
This is exactly the shape required by the
`transversal_paths_meet_in_rectangle` lemma for the horizontal path
(endpoints on the left/right edges of a rectangle). -/
theorem path_reparametrized_on_neg_one_one {S : Set Plane} {a b : Plane} (hj : JoinedIn S a b) :
    ∃ h : ℝ → Plane, ContinuousOn h (Icc (-1:ℝ) 1) ∧ h (-1) = a ∧ h 1 = b ∧
      ∀ t ∈ Icc (-1:ℝ) 1, h t ∈ S := by
  refine ⟨fun t => hj.somePath (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)),
    ?_, ?_, ?_, ?_⟩
  · exact (hj.somePath.continuous.comp
      (continuous_projIcc.comp (by fun_prop))).continuousOn
  · change hj.somePath _ = a
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.source
  · change hj.somePath _ = b
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.target
  · intro t _; exact hj.somePath_mem _

/-- **Math.** **Setup 2 (segment meets curve).** The vertical segment from `s = !₂[0,-2]` to
`n = !₂[0,2]` meets the curve.  Proof via the
`transversal_paths_meet_in_rectangle` lemma with horizontal path
`h` a curve-path from `a = !₂[-1,0]` to `b = !₂[1,0]` (the curve is path-connected,
reparametrized by `path_reparametrized_on_neg_one_one`) staying in the rectangle `[-1,1]×[-2,2]`
(`normalized_subset_rectangle`), and vertical path `v t = !₂[0, 2t]` running from the
bottom edge `y=-2` to the top edge `y=2`.  Delivers a curve point on the vertical
axis. -/
theorem segment_meets_curve (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (_hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ p ∈ range r, p 0 = 0 ∧ p 1 ∈ Icc (-2:ℝ) 2 := by
  -- the curve is path-connected (continuous image of the path-connected circle)
  have hsp : IsPathConnected (sphere (0:Plane) 1) :=
    isPathConnected_sphere one_lt_rank_plane 0 (by norm_num)
  haveI : PathConnectedSpace ↥(sphere (0:Plane) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsp
  have h1 : IsPathConnected (univ : Set ↥(sphere (0:Plane) 1)) :=
    pathConnectedSpace_iff_univ.mp ‹_›
  have hpc : IsPathConnected (range r) := by
    have := h1.image hcont; rwa [image_univ] at this
  have hjoin : JoinedIn (range r) (normalizedLeftEnd) (normalizedRightEnd) :=
    hpc.joinedIn _ hm _ hp
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := path_reparametrized_on_neg_one_one hjoin
  have hrect := normalized_subset_rectangle hm hp hfar
  -- vertical path `v t = !₂[0, 2t]`
  set v : ℝ → Plane := fun t => !₂[(0:ℝ), 2 * t] with hvdef
  have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) := by
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hv0 : ∀ t : ℝ, v t 0 = 0 := by intro t; simp [hvdef]
  have hv1 : ∀ t : ℝ, v t 1 = 2 * t := by intro t; simp [hvdef]
  -- edge/rectangle conditions
  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hrect (hhmem t ht)
  have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rw [mem_Icc] at ht
    refine ⟨?_, ?_⟩
    · rw [hv0]; simp
    · rw [hv1, mem_Icc]; constructor <;> nlinarith [ht.1, ht.2]
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  have hv1e : v (-1) 1 = -2 := by rw [hv1]; norm_num
  have hv2e : v 1 1 = 2 := by rw [hv1]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := transversal_paths_meet_in_rectangle hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1e hv2e
  refine ⟨h s, hhmem s hs, ?_, ?_⟩
  · rw [heq, hv0]
  · rw [heq]; exact (hvE t ht).2

/-- **Math.** **Setup 3 (top of the axis).** The intersection of the curve with the vertical
axis `Jax = {p ∈ range r | p 0 = 0}` is compact (closed subset of the compact
curve) and nonempty (`segment_meets_curve`), hence attains its `y`-maximum at some
point `l ∈ range r` with `l 0 = 0`. -/
theorem exists_highest_point_of_curve_on_axis (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ l ∈ range r, l 0 = 0 ∧ ∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1 := by
  set Jax : Set Plane := {p ∈ range r | p 0 = 0} with hJax
  have hsub : Jax ⊆ range r := fun p hp => hp.1
  have hJaxcl : IsClosed Jax :=
    (jordanCurve_isClosed r hcont).inter (isClosed_eq (by fun_prop) continuous_const)
  have hJaxcpt : IsCompact Jax :=
    (jordanCurve_isCompact r hcont).of_isClosed_subset hJaxcl hsub
  have hne : Jax.Nonempty := by
    obtain ⟨p, hpr, hp0, _⟩ := segment_meets_curve hbr hcont hinj hm hp hfar
    exact ⟨p, hpr, hp0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨l, hlJax, hlmax⟩ :=
    hJaxcpt.exists_isMaxOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  refine ⟨l, hlJax.1, hlJax.2, ?_⟩
  intro p hpr hp0
  exact hlmax (show p ∈ Jax from ⟨hpr, hp0⟩)

/-- **Math.** **Image of an arc under the subtype coercion is again an arc.** If `A ⊆ ↥K`
(a subset of a subtype of `Plane`) is homeomorphic to `unitInterval`, then its image
`(↑) '' A ⊆ Plane` is homeomorphic to `unitInterval`.  The composite coercion
`↥A → Plane` is a continuous injection from a compact space to a Hausdorff space,
hence a (closed) embedding, so `↥A ≃ₜ ↥(range …) = ↥((↑) '' A)`. -/
private lemma arc_in_plane_homeo_unitInterval {K : Set Plane} {A : Set ↥K}
    (e : A ≃ₜ unitInterval) : Nonempty (((↑) '' A : Set Plane) ≃ₜ unitInterval) := by
  haveI : CompactSpace ↥A := e.symm.compactSpace
  let k : ↥A → Plane := fun a => ((a : ↥K) : Plane)
  have hkc : Continuous k := continuous_subtype_val.comp continuous_subtype_val
  have hki : Injective k := Subtype.coe_injective.comp Subtype.coe_injective
  have hemb : Topology.IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  have hrange : Set.range k = ((↑) '' A : Set Plane) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨((Homeomorph.setCongr hrange).symm.trans hemb.toHomeomorph.symm).trans e⟩

/-- **Math.** **Setup 4 (arc split at `a`, `b`).** The curve `range r` splits at the farthest
pair `a = !₂[-1,0]`, `b = !₂[1,0]` into two closed arcs `J_n`, `J_s ⊆ Plane`, each
`≃ₜ unitInterval`, with `J_n ∪ J_s = range r` and `J_n ∩ J_s = {a, b}`, labelled so
that the `y`-topmost axis point `l` lies in `J_n`. -/
theorem exists_arc_decomposition_of_curve (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : normalizedLeftEnd ∈ range r) (hp : normalizedRightEnd ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ J_n J_s : Set Plane,
      IsClosed J_n ∧ IsClosed J_s ∧
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {normalizedLeftEnd, normalizedRightEnd} ∧
      Nonempty (J_n ≃ₜ unitInterval) ∧ Nonempty (J_s ≃ₜ unitInterval) ∧
      IsPathConnected (J_n \ {normalizedLeftEnd, normalizedRightEnd}) ∧
      IsPathConnected (J_s \ {normalizedLeftEnd, normalizedRightEnd}) ∧
      ∃ l ∈ range r, l 0 = 0 ∧ (∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1) ∧ l ∈ J_n := by
  obtain ⟨l, hlr, hl0, hlmax⟩ := exists_highest_point_of_curve_on_axis hbr hcont hinj hm hp hfar
  set J := jordanCurveHomeo r hcont hinj with hJdef
  have hab : normalizedLeftEnd ≠ normalizedRightEnd := by
    intro h
    have h0 : normalizedLeftEnd 0 = normalizedRightEnd 0 := by rw [h]
    rw [show normalizedLeftEnd 0 = -1 from by simp,
        show normalizedRightEnd 0 = 1 from by simp] at h0
    norm_num at h0
  set x : sphere (0 : Plane) 1 := J.symm ⟨_, hm⟩ with hxdef
  set y : sphere (0 : Plane) 1 := J.symm ⟨_, hp⟩ with hydef
  have hxy : x ≠ y := by
    intro h
    exact hab (Subtype.ext_iff.mp (J.symm.injective h))
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpcA1, hpcA2⟩ := Arcs.jordanCurve_split J hxy
  -- transported endpoints: `J x = ⟨a,hm⟩`, `J y = ⟨b,hp⟩`
  have hJx : J x = ⟨_, hm⟩ := J.apply_symm_apply _
  have hJy : J y = ⟨_, hp⟩ := J.apply_symm_apply _
  -- planar images of the two arcs
  set B₁ : Set Plane := (↑) '' A₁ with hB1
  set B₂ : Set Plane := (↑) '' A₂ with hB2
  have hBu : B₁ ∪ B₂ = range r := by
    rw [hB1, hB2, ← Set.image_union, hu, Set.image_univ, Subtype.range_coe]
  have hBi : B₁ ∩ B₂ = {normalizedLeftEnd, normalizedRightEnd} := by
    rw [hB1, hB2, ← Set.image_inter Subtype.coe_injective, hi, hJx, hJy,
      Set.image_pair]
  have hn1 : Nonempty (B₁ ≃ₜ unitInterval) := arc_in_plane_homeo_unitInterval e1
  have hn2 : Nonempty (B₂ ≃ₜ unitInterval) := arc_in_plane_homeo_unitInterval e2
  have hcl1 : IsClosed B₁ :=
    (isCompact_iff_compactSpace.mpr hn1.some.symm.compactSpace).isClosed
  have hcl2 : IsClosed B₂ :=
    (isCompact_iff_compactSpace.mpr hn2.some.symm.compactSpace).isClosed
  -- transport path-connectedness of the arc interiors down to the plane
  have hpcB1 : IsPathConnected (B₁ \ {normalizedLeftEnd, normalizedRightEnd}) := by
    have h := hpcA1.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  have hpcB2 : IsPathConnected (B₂ \ {normalizedLeftEnd, normalizedRightEnd}) := by
    have h := hpcA2.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  -- `l` lies in `range r = B₁ ∪ B₂`; label the containing arc `J_n`
  have hlB : l ∈ B₁ ∪ B₂ := by rw [hBu]; exact hlr
  rcases hlB with hl | hl
  · exact ⟨B₁, B₂, hcl1, hcl2, hBu, hBi, hn1, hn2, hpcB1, hpcB2, l, hlr, hl0, hlmax, hl⟩
  · refine ⟨B₂, B₁, hcl2, hcl1, ?_, ?_, hn2, hn1, hpcB2, hpcB1, l, hlr, hl0, hlmax, hl⟩
    · rw [Set.union_comm]; exact hBu
    · rw [Set.inter_comm]; exact hBi

end JordanCurve
