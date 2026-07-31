/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Normalization.Setup

@[expose] public section

/-!
# Concatenating paths

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

namespace JordanCurve

open Metric Set Function Bornology

/-! ### Path-concatenation infrastructure and Maehara's interior points

The tools below package repeated use of the `crossing` lemma: any bottom-to-top
path in the normalized rectangle meets each arc (`vertical_meets_arc`), together with
the plumbing (`concatPath2`, `concatPath3`) that glues path pieces into one
continuous path on `[-1,1]` whose image is the union of the pieces. -/

/-- **Math.** An arc `J ⊆ Plane` homeomorphic to `unitInterval` is path-connected. -/
theorem arc_isPathConnected {J : Set Plane} (e : ↥J ≃ₜ unitInterval) :
    IsPathConnected J := by
  haveI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0:ℝ) 1).isPathConnected (Set.nonempty_Icc.mpr (by norm_num)))
  have h1 : IsPathConnected (univ : Set unitInterval) := isPathConnected_univ
  have h2 := h1.image
    (show Continuous (fun x : unitInterval => ((e.symm x : ↥J) : Plane)) from
      continuous_subtype_val.comp e.symm.continuous)
  rw [Set.image_univ] at h2
  have hrange : (Set.range fun x : unitInterval => ((e.symm x : ↥J) : Plane)) = J := by
    ext p
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact (e.symm x).2
    · intro hp; exact ⟨e ⟨p, hp⟩, by simp⟩
  rwa [hrange] at h2

/-- **Math.** An arc `J ≃ₜ unitInterval` joins any two of its points inside `J`. -/
theorem arc_joinedIn {J : Set Plane} (e : ↥J ≃ₜ unitInterval)
    {a b : Plane} (ha : a ∈ J) (hb : b ∈ J) : JoinedIn J a b :=
  (arc_isPathConnected e).joinedIn a ha b hb

/-- **Math.** **Key reusable tool.** Any path `v` running from the bottom edge (`v (-1) 1 = -2`)
to the top edge (`v 1 1 = 2`) of the normalized rectangle `[-1,1]×[-2,2]` must meet an
arc `J` that joins the left point `a = !₂[-1,0]` to the right point `b = !₂[1,0]` inside
the rectangle.  Immediate from `crossing`, using `arc_path` for the horizontal path. -/
theorem vertical_meets_arc (hbr : BrouwerFPT) {J : Set Plane}
    (hJsub : J ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2})
    (hJoin : JoinedIn J (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {v : ℝ → Plane} (hvcont : ContinuousOn v (Icc (-1:ℝ) 1))
    (hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2)
    (hv1 : v (-1) 1 = -2) (hv2 : v 1 1 = 2) :
    ∃ t ∈ Icc (-1:ℝ) 1, v t ∈ J := by
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hJoin
  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hJsub (hhmem t ht)
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1 hv2
  exact ⟨t, ht, heq ▸ hhmem s hs⟩

/-- **Math.** A path piece `f : ℝ → Plane`, continuous on `[-1,1]`, as a `Path (f (-1)) (f 1)`
over `unitInterval` (reparametrized by `s ↦ 2s-1`). -/
private noncomputable def pathOfPiece {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) : Path (f (-1)) (f 1) :=
  Path.mk ⟨fun s : unitInterval => f (2 * (s : ℝ) - 1), by
      refine hf.comp_continuous (by fun_prop) (fun s => ?_)
      have hs := s.2; rw [Set.mem_Icc] at hs ⊢
      constructor <;> [linarith [hs.1]; linarith [hs.2]]⟩
    (by norm_num [Set.Icc.coe_zero]) (by norm_num [Set.Icc.coe_one])

private lemma pathOfPiece_range {f : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨s, rfl⟩
    have hs := s.2; rw [Set.mem_Icc] at hs
    exact ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨⟨(y + 1) / 2, by rw [Set.mem_Icc]; constructor <;> linarith⟩, ?_⟩
    show f (2 * ((y + 1) / 2) - 1) = f y
    congr 1; ring

/-- **Math.** **Path concatenation (2 pieces).** Two path pieces on `[-1,1]` that chain up
(`f 1 = g (-1)`) glue to one path `c` on `[-1,1]` from `f (-1)` to `g 1`, whose image
is contained in the union of the pieces' images. -/
theorem concatPath2 {f g : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hchain : f 1 = g (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = g 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1, c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 := by
  set P : Path (f (-1)) (g 1) :=
    (pathOfPiece hf).trans ((pathOfPiece hg).cast hchain rfl) with hP
  refine ⟨fun t => P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)), ?_, ?_, ?_, ?_⟩
  · exact (P.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
  · show P _ = f (-1)
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.source
  · show P _ = g 1
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact P.target
  · intro t _
    have hmem : P (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)) ∈ Set.range P := ⟨_, rfl⟩
    rw [hP, Path.trans_range] at hmem
    have hr1 : Set.range (pathOfPiece hf) = f '' Icc (-1:ℝ) 1 := pathOfPiece_range hf
    have hr2 : Set.range ((pathOfPiece hg).cast hchain rfl) = g '' Icc (-1:ℝ) 1 := by
      simp only [Path.cast_coe]; exact pathOfPiece_range hg
    rw [hr1, hr2] at hmem
    exact hmem

/-- **Math.** **Path concatenation (3 pieces).** Three chained path pieces on `[-1,1]` glue to
one path `c` on `[-1,1]` from `f (-1)` to `h 1`, with image in the union of the three
pieces' images. -/
theorem concatPath3 {f g h : ℝ → Plane}
    (hf : ContinuousOn f (Icc (-1:ℝ) 1)) (hg : ContinuousOn g (Icc (-1:ℝ) 1))
    (hh : ContinuousOn h (Icc (-1:ℝ) 1))
    (hfg : f 1 = g (-1)) (hgh : g 1 = h (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f (-1) ∧ c 1 = h 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ f '' Icc (-1:ℝ) 1 ∪ g '' Icc (-1:ℝ) 1 ∪ h '' Icc (-1:ℝ) 1 := by
  obtain ⟨c2, hc2cont, hc2a, hc2b, hc2mem⟩ := concatPath2 hf hg hfg
  obtain ⟨c3, hc3cont, hc3a, hc3b, hc3mem⟩ :=
    concatPath2 hc2cont hh (by rw [hc2b]; exact hgh)
  refine ⟨c3, hc3cont, by rw [hc3a, hc2a], hc3b, fun t ht => ?_⟩
  rcases hc3mem t ht with hin | hin
  · obtain ⟨u, hu, huc⟩ := hin
    exact Set.mem_union_left _ (huc ▸ hc2mem u hu)
  · exact Set.mem_union_right _ hin

/-- **Math.** **Path concatenation (5 pieces).** Five chained path pieces on `[-1,1]` glue to one
path `c` on `[-1,1]` from `f1 (-1)` to `f5 1`, with image in the union of the five
pieces' images. -/
theorem concatPath5 {f1 f2 f3 f4 f5 : ℝ → Plane}
    (h1 : ContinuousOn f1 (Icc (-1:ℝ) 1)) (h2 : ContinuousOn f2 (Icc (-1:ℝ) 1))
    (h3 : ContinuousOn f3 (Icc (-1:ℝ) 1)) (h4 : ContinuousOn f4 (Icc (-1:ℝ) 1))
    (h5 : ContinuousOn f5 (Icc (-1:ℝ) 1))
    (c12 : f1 1 = f2 (-1)) (c23 : f2 1 = f3 (-1)) (c34 : f3 1 = f4 (-1))
    (c45 : f4 1 = f5 (-1)) :
    ∃ c : ℝ → Plane, ContinuousOn c (Icc (-1:ℝ) 1) ∧ c (-1) = f1 (-1) ∧ c 1 = f5 1 ∧
      ∀ t ∈ Icc (-1:ℝ) 1,
        c t ∈ ((((f1 '' Icc (-1:ℝ) 1 ∪ f2 '' Icc (-1:ℝ) 1) ∪ f3 '' Icc (-1:ℝ) 1)
          ∪ f4 '' Icc (-1:ℝ) 1) ∪ f5 '' Icc (-1:ℝ) 1) := by
  obtain ⟨c123, hc123cont, hc123a, hc123b, hc123mem⟩ := concatPath3 h1 h2 h3 c12 c23
  obtain ⟨c45, hc45cont, hc45a, hc45b, hc45mem⟩ := concatPath2 h4 h5 c45
  obtain ⟨c, hccont, hca, hcb, hcmem⟩ :=
    concatPath2 hc123cont hc45cont (by rw [hc123b, hc45a]; exact c34)
  refine ⟨c, hccont, by rw [hca, hc123a], by rw [hcb, hc45b], fun t ht => ?_⟩
  rcases hcmem t ht with hin | hin
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc123mem u hu
    rw [hue] at hmem
    exact Or.inl (Or.inl hmem)
  · obtain ⟨u, hu, hue⟩ := hin
    have hmem := hc45mem u hu
    rw [hue] at hmem
    rcases hmem with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- **Math.** **Interior point `m`.** The intersection `J_n ∩ axis` (`axis = {p | p 0 = 0}`) is
compact and nonempty (it contains `l`), hence attains its `y`-minimum at a point `m`. -/
theorem exists_ymin_Jn_axis {J_n : Set Plane} (hJncl : IsClosed J_n)
    (hcpt : IsCompact J_n) {l : Plane} (hlJn : l ∈ J_n) (hl0 : l 0 = 0) :
    ∃ m ∈ J_n, m 0 = 0 ∧ ∀ p ∈ J_n, p 0 = 0 → m 1 ≤ p 1 := by
  set Jm : Set Plane := {p ∈ J_n | p 0 = 0} with hJm
  have hsub : Jm ⊆ J_n := fun p hp => hp.1
  have hcl : IsClosed Jm :=
    hJncl.inter (isClosed_eq (by fun_prop) continuous_const)
  have hJmcpt : IsCompact Jm := hcpt.of_isClosed_subset hcl hsub
  have hne : Jm.Nonempty := ⟨l, hlJn, hl0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨m, hmJm, hmmin⟩ :=
    hJmcpt.exists_isMinOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  exact ⟨m, hmJm.1, hmJm.2, fun p hpJn hp0 => hmmin (show p ∈ Jm from ⟨hpJn, hp0⟩)⟩

end JordanCurve
