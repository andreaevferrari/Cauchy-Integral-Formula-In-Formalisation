/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Defs

/-!
# Maehara's crossing lemma

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** **Lemma 2 (crossing lemma, Maehara).** Two continuous paths in a rectangle
`[a,b]×[c,d]`, one running from the left edge to the right edge (`h`), the other
from the bottom edge to the top edge (`v`), must meet. Proved directly from
Brouwer: if they were disjoint, the explicit normalized map
`F(s,t) = ((v₁ t − h₁ s)/N, (h₂ s − v₂ t)/N)` (with `N` the sup-norm of
`h s − v t`) sends the parameter square `[-1,1]²` to its boundary with no fixed
point. Coordinates are `p 0`, `p 1` of `p : Plane`. -/
theorem transversal_paths_meet_in_rectangle
  (hbr : BrouwerFPT) {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d)
    (h v : ℝ → Plane)
    (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
    (hhE : ∀ t ∈ Icc (-1 : ℝ) 1, h t 0 ∈ Icc a b ∧ h t 1 ∈ Icc c d)
    (hvE : ∀ t ∈ Icc (-1 : ℝ) 1, v t 0 ∈ Icc a b ∧ v t 1 ∈ Icc c d)
    (hh1 : h (-1) 0 = a) (hh2 : h 1 0 = b)
    (hv1 : v (-1) 1 = c) (hv2 : v 1 1 = d) :
    ∃ s ∈ Icc (-1:ℝ) 1, ∃ t ∈ Icc (-1:ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ s ∈ Icc (-1) 1, ∀ t ∈ Icc (-1) 1, h s ≠ v t`
  -- The parameter square `Q = [-1,1]²`.
  set Q : Set Plane := {p | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-1:ℝ) 1} with hQdef
  have hQ0 : ∀ p ∈ Q, p 0 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.1
  have hQ1 : ∀ p ∈ Q, p 1 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.2
  -- `Q` is convex.
  have hconv : Convex ℝ Q := by
    have c0 : Convex ℝ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
    have c1 : Convex ℝ {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
    exact c0.inter c1
  -- `Q` is compact (closed and bounded in a finite-dimensional space).
  have hcomp : IsCompact Q := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have d0 : IsClosed {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (0:Fin 2)).continuous
      have d1 : IsClosed {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (1:Fin 2)).continuous
      exact d0.inter d1
    · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 2)).subset
      intro p hp
      simp only [mem_closedBall, dist_zero_right]
      have h0 : |p 0| ≤ 1 := abs_le.2 ⟨hp.1.1, hp.1.2⟩
      have h1 : |p 1| ≤ 1 := abs_le.2 ⟨hp.2.1, hp.2.2⟩
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by ring, Real.sqrt_sq]; norm_num]
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  have hne0 : Q.Nonempty := by
    refine ⟨0, ?_, ?_⟩ <;>
      · simp only [mem_Icc, show (0:Plane) 0 = 0 from rfl, show (0:Plane) 1 = 0 from rfl]
        norm_num
  -- The sup-norm distance and the normalized boundary map.
  let N : Plane → ℝ := fun p => max |h (p 0) 0 - v (p 1) 0| |h (p 0) 1 - v (p 1) 1|
  let n0 : Plane → ℝ := fun p => (v (p 1) 0 - h (p 0) 0) / N p
  let n1 : Plane → ℝ := fun p => (h (p 0) 1 - v (p 1) 1) / N p
  let F : Plane → Plane := fun p => !₂[n0 p, n1 p]
  have hNnn : ∀ p, 0 ≤ N p := fun p => le_trans (abs_nonneg _) (le_max_left _ _)
  -- `N > 0` on `Q`: otherwise `h (p 0) = v (p 1)`, contradicting `hcon`.
  have hNpos : ∀ p ∈ Q, 0 < N p := by
    intro p hp
    rcases (hNnn p).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hNz : N p = 0 := heq.symm
      have hA0 : |h (p 0) 0 - v (p 1) 0| ≤ N p := le_max_left _ _
      have hB0 : |h (p 0) 1 - v (p 1) 1| ≤ N p := le_max_right _ _
      rw [hNz] at hA0 hB0
      have eA : h (p 0) 0 = v (p 1) 0 := by
        have := le_antisymm hA0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      have eB : h (p 0) 1 = v (p 1) 1 := by
        have := le_antisymm hB0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      refine hcon (p 0) (hQ0 p hp) (p 1) (hQ1 p hp) ?_
      ext i; fin_cases i
      · exact eA
      · exact eB
  -- Continuity ingredients.
  have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have mt0 : MapsTo (fun p : Plane => p 0) Q (Icc (-1:ℝ) 1) := fun p hp => hQ0 p hp
  have mt1 : MapsTo (fun p : Plane => p 1) Q (Icc (-1:ℝ) 1) := fun p hp => hQ1 p hp
  have hHx0 : ContinuousOn (fun p : Plane => h (p 0) 0) Q :=
    (hc0.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hHx1 : ContinuousOn (fun p : Plane => h (p 0) 1) Q :=
    (hc1.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hVx0 : ContinuousOn (fun p : Plane => v (p 1) 0) Q :=
    (hc0.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hVx1 : ContinuousOn (fun p : Plane => v (p 1) 1) Q :=
    (hc1.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hNcont : ContinuousOn N Q :=
    ContinuousOn.sup ((hHx0.sub hVx0).abs) ((hHx1.sub hVx1).abs)
  have hn0c : ContinuousOn n0 Q :=
    (hVx0.sub hHx0).div hNcont (fun p hp => (hNpos p hp).ne')
  have hn1c : ContinuousOn n1 Q :=
    (hHx1.sub hVx1).div hNcont (fun p hp => (hNpos p hp).ne')
  have hFcont : ContinuousOn F Q := by
    have hG : ContinuousOn (fun p : Plane => (![n0 p, n1 p] : Fin 2 → ℝ)) Q := by
      rw [continuousOn_pi]
      intro i; fin_cases i
      · simpa using hn0c
      · simpa using hn1c
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn hG
  -- `F` maps `Q` into `Q`: each coordinate has absolute value `≤ 1`.
  have hbound : ∀ p ∈ Q, |n0 p| ≤ 1 ∧ |n1 p| ≤ 1 := by
    intro p hp
    have hN := hNpos p hp
    refine ⟨?_, ?_⟩
    · change |(v (p 1) 0 - h (p 0) 0) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      calc |v (p 1) 0 - h (p 0) 0| = |h (p 0) 0 - v (p 1) 0| := abs_sub_comm _ _
        _ ≤ N p := le_max_left _ _
    · change |(h (p 0) 1 - v (p 1) 1) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      exact le_max_right _ _
  have hmaps : MapsTo F Q Q := by
    intro p hp
    obtain ⟨hb0, hb1⟩ := hbound p hp
    exact ⟨mem_Icc.2 (abs_le.1 hb0), mem_Icc.2 (abs_le.1 hb1)⟩
  -- Package as a self-map of `Q` and apply Brouwer.
  let f : C(Q, Q) := ⟨fun p => ⟨F p.1, hmaps p.2⟩, by
    apply Continuous.subtype_mk; exact hFcont.restrict⟩
  obtain ⟨x, hx⟩ := hbr Q hconv hcomp hne0 f
  set p₀ : Plane := (x : Plane) with hp0def
  have hp0Q : p₀ ∈ Q := x.2
  have hN := hNpos p₀ hp0Q
  have hfix : F p₀ = p₀ := congrArg Subtype.val hx
  have hfix0 : p₀ 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := by
    have e : (F p₀) 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := rfl
    rw [← e, hfix]
  have hfix1 : p₀ 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := by
    have e : (F p₀) 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := rfl
    rw [← e, hfix]
  -- The fixed point lies on the boundary: `|p₀ 0| = 1` or `|p₀ 1| = 1`.
  have a0 : |p₀ 0| = |h (p₀ 0) 0 - v (p₀ 1) 0| / N p₀ := by
    conv_lhs => rw [hfix0]
    rw [abs_div, abs_of_pos hN, abs_sub_comm]
  have a1 : |p₀ 1| = |h (p₀ 0) 1 - v (p₀ 1) 1| / N p₀ := by
    conv_lhs => rw [hfix1]
    rw [abs_div, abs_of_pos hN]
  have hbdry : |p₀ 0| = 1 ∨ |p₀ 1| = 1 := by
    rcases le_total |h (p₀ 0) 1 - v (p₀ 1) 1| |h (p₀ 0) 0 - v (p₀ 1) 0| with hle | hle
    · left
      have hNA : N p₀ = |h (p₀ 0) 0 - v (p₀ 1) 0| := max_eq_left hle
      rw [a0, hNA]; exact div_self (by rw [← hNA]; exact hN.ne')
    · right
      have hNB : N p₀ = |h (p₀ 0) 1 - v (p₀ 1) 1| := max_eq_right hle
      rw [a1, hNB]; exact div_self (by rw [← hNB]; exact hN.ne')
  -- Boundary contradiction in each of the four cases.
  rcases hbdry with hb | hb
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 0 = 1`: then `h (p₀ 0) 0 = b ≥ v (p₀ 1) 0`, so `p₀ 0 ≤ 0`.
      have hh0b : h (p₀ 0) 0 = b := by rw [hpos]; exact hh2
      have hvle : v (p₀ 1) 0 ≤ b := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.2
      have : p₀ 0 ≤ 0 := by
        rw [hfix0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 0 = -1`: then `h (p₀ 0) 0 = a ≤ v (p₀ 1) 0`, so `p₀ 0 ≥ 0`.
      have hh0a : h (p₀ 0) 0 = a := by rw [hneg]; exact hh1
      have hvge : a ≤ v (p₀ 1) 0 := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.1
      have : 0 ≤ p₀ 0 := by rw [hfix0]; exact div_nonneg (by linarith) hN.le
      linarith
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 1 = 1`: then `v (p₀ 1) 1 = d ≥ h (p₀ 0) 1`, so `p₀ 1 ≤ 0`.
      have hv1d : v (p₀ 1) 1 = d := by rw [hpos]; exact hv2
      have hhle : h (p₀ 0) 1 ≤ d := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.2
      have : p₀ 1 ≤ 0 := by
        rw [hfix1]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 1 = -1`: then `v (p₀ 1) 1 = c ≤ h (p₀ 0) 1`, so `p₀ 1 ≥ 0`.
      have hv1c : v (p₀ 1) 1 = c := by rw [hneg]; exact hv1
      have hhge : c ≤ h (p₀ 0) 1 := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.1
      have : 0 ≤ p₀ 1 := by rw [hfix1]; exact div_nonneg (by linarith) hN.le
      linarith

end JordanCurve
