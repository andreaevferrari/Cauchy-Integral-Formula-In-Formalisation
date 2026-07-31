/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Arcs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UnitInterval

/-!
# Toward the 2D Brouwer fixed point theorem

We build the classical topological proof of the two-dimensional Brouwer fixed
point theorem, in four phases:

* **Phase 1** — the once-around loop on `AddCircle 1` is not homotopic (rel
  endpoints) to the constant loop.  This is the mathematical heart: it is proved
  from the covering `ℝ → AddCircle 1` via unique path lifting
  (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
* **Phase 1.5** — transport of Phase 1 across `AddCircle 1 ≃ₜ Circle ≃ₜ
  sphere (0:ℝ²) 1` to obtain a non-nullhomotopic loop on the geometric circle.
* **Phase 2** — no retraction of the disk onto its boundary circle: a retraction
  would give a null-homotopy of the Phase 1.5 loop.
* **Phase 3** — Brouwer for the closed unit disk (`brouwer_disk`): a
  fixed-point-free self-map yields a retraction (ray construction).
* **Phase 4** — the general convex/compact/nonempty statement `brouwerFPT`.
-/

@[expose] public section

namespace JordanCurve.Brouwer

open Metric Set Function unitInterval Topology
open scoped RealInnerProductSpace

/-- **Eng.** The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Phase 1 — the once-around loop on `AddCircle 1` is not nullhomotopic -/

/-- **Math.** The covering map `ℝ → AddCircle 1`. -/
theorem realCoveringAddCircle : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

/-- **Math.** The once-around loop `t ↦ ↑t` in `AddCircle 1`. -/
noncomputable def addCircleLoop : C(I, AddCircle (1 : ℝ)) :=
  ⟨fun t => ((t : ℝ) : AddCircle (1 : ℝ)),
    realCoveringAddCircle.continuous.comp continuous_subtype_val⟩

/-- **Math.** The lift of `addCircleLoop` to `ℝ` starting at `0`: the identity `t ↦ ↑t`. -/
noncomputable def identityPathLift : C(I, ℝ) := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

@[simp] lemma acLoop_apply (t : I) : addCircleLoop t = ((t : ℝ) : AddCircle (1 : ℝ)) := rfl
@[simp] lemma idLift_apply (t : I) : identityPathLift t = (t : ℝ) := rfl

/-- **Math.** **Phase 1.** The once-around loop is not homotopic rel endpoints to the
constant loop. -/
theorem addCircleLoop_not_homotopic :
    ¬ addCircleLoop.HomotopicRel (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) {0, 1} := by
  intro h
  have h0 : addCircleLoop 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by simp
  have h1 : (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simp
  have key := realCoveringAddCircle.liftPath_apply_one_eq_of_homotopicRel h (0 : ℝ) h0 h1
  -- Identify the two lifts.
  have e1 : realCoveringAddCircle.liftPath addCircleLoop (0 : ℝ) h0 = identityPathLift := by
    refine ((realCoveringAddCircle.eq_liftPath_iff' h0).mpr ⟨?_, ?_⟩).symm
    · ext t; simp
    · simp
  have e2 : realCoveringAddCircle.liftPath
      (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) (0 : ℝ) h1
      = ContinuousMap.const I (0 : ℝ) := realCoveringAddCircle.liftPath_const h1
  rw [e1, e2] at key
  simp at key

/-! ## Phase 1.5 — transport to the geometric circle `sphere (0:ℝ²) 1` -/

/-- **Math.** The homeomorphism `AddCircle 1 ≃ₜ sphere (0:ℝ²) 1`, via `Circle`. -/
noncomputable def addCircleHomeoSphere : AddCircle (1 : ℝ) ≃ₜ sphere (0 : Plane) 1 :=
  (AddCircle.homeomorphCircle (one_ne_zero)).trans Arcs.circleHomeoSphere

/-- **Math.** The base point of the sphere loop. -/
noncomputable def sphereBasePoint : sphere (0 : Plane) 1 := addCircleHomeoSphere 0

/-- **Math.** The once-around loop on the geometric circle `sphere (0:ℝ²) 1`. -/
noncomputable def sphereLoop : C(I, sphere (0 : Plane) 1) :=
  (⟨addCircleHomeoSphere, addCircleHomeoSphere.continuous⟩ : C(AddCircle (1 : ℝ),
    sphere (0 : Plane) 1)).comp addCircleLoop

@[simp] lemma sLoop_apply (t : I) : sphereLoop t = addCircleHomeoSphere (addCircleLoop t) := rfl

lemma sphereLoop_zero : sphereLoop 0 = sphereBasePoint := by simp [sphereBasePoint]

/-- **Math.** **Phase 1.5.** The once-around loop on the geometric circle is not homotopic
rel endpoints to the constant loop. -/
theorem sphereLoop_not_homotopic :
    ¬ sphereLoop.HomotopicRel (ContinuousMap.const I sphereBasePoint) {0, 1} := by
  intro h
  apply addCircleLoop_not_homotopic
  have hh := h.comp_continuousMap
    (⟨addCircleHomeoSphere.symm, addCircleHomeoSphere.symm.continuous⟩ : C(sphere (0 : Plane) 1,
      AddCircle (1 : ℝ)))
  have e1 : (⟨addCircleHomeoSphere.symm, addCircleHomeoSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp sphereLoop = addCircleLoop := by
    ext t; simp [sphereLoop, addCircleHomeoSphere.symm_apply_apply]
  have e2 : (⟨addCircleHomeoSphere.symm, addCircleHomeoSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp (ContinuousMap.const I sphereBasePoint)
      = ContinuousMap.const I (0 : AddCircle (1 : ℝ)) := by
    ext t; simp [sphereBasePoint, addCircleHomeoSphere.symm_apply_apply]
  rwa [e1, e2] at hh

lemma sphereLoop_one : sphereLoop 1 = sphereBasePoint := by
  have : addCircleLoop 1 = (0 : AddCircle (1 : ℝ)) := by
    simp only [acLoop_apply]
    have : ((1 : I) : ℝ) = (1 : ℝ) := rfl
    rw [this]; exact AddCircle.coe_period 1
  simp [sphereBasePoint, this]

/-! ## Phase 2 — no retraction of the disk onto its boundary circle -/

/-- **Math.** The straight-line contraction point `(1-t)·(loop s) + t·base` in the disk. -/
noncomputable def diskBoundaryPoint (t s : I) : Plane :=
  (1 - (t : ℝ)) • (sphereLoop s : Plane) + (t : ℝ) • (sphereBasePoint : Plane)

lemma diskBoundaryPoint_mem (t s : I) : diskBoundaryPoint t s ∈ closedBall (0 : Plane) 1 := by
  have hv : (sphereLoop s : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall (sphereLoop s).2
  have hw : (sphereBasePoint : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall sphereBasePoint.2
  exact convex_closedBall 0 1 hv hw (by unit_interval) (by unit_interval) (by ring)

lemma continuous_diskBoundaryPoint : Continuous (fun p : I × I => diskBoundaryPoint p.1 p.2) := by
  unfold diskBoundaryPoint
  fun_prop

/-- **Math.** The contraction as a continuous map into the disk. -/
noncomputable def diskNullhomotopy : C(I × I, closedBall (0 : Plane) 1) :=
  ⟨fun p => ⟨diskBoundaryPoint p.1 p.2, diskBoundaryPoint_mem p.1 p.2⟩,
    (continuous_diskBoundaryPoint).subtype_mk _⟩

/-- **Math.** **Phase 2.** There is no retraction of the closed disk onto its boundary
circle. -/
theorem no_retraction (ρ : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))
    (hrange : ∀ x, (ρ x : Plane) ∈ sphere (0 : Plane) 1)
    (hid : ∀ x : closedBall (0 : Plane) 1,
      (x : Plane) ∈ sphere (0 : Plane) 1 → (ρ x : Plane) = (x : Plane)) :
    False := by
  apply sphereLoop_not_homotopic
  -- The homotopy `H t s = ρ ((1-t)·loop s + t·base)`, valued in the sphere.
  set H : C(I × I, sphere (0 : Plane) 1) :=
    ⟨fun p => ⟨(ρ (diskNullhomotopy p) : Plane), hrange _⟩,
      (map_continuous ρ |>.comp (map_continuous diskNullhomotopy)).subtype_val.subtype_mk _⟩ with hH
  refine ⟨{
    toContinuousMap := H
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · -- H (0, s) = sphereLoop s
    intro s
    have hmem : (diskNullhomotopy (0, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskBoundaryPoint 0 s ∈ _
      simp only [diskBoundaryPoint, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
      exact (sphereLoop s).2
    apply Subtype.ext
    change (ρ (diskNullhomotopy (0, s)) : Plane) = (sphereLoop s : Plane)
    rw [hid _ hmem]
    show (diskNullhomotopy (0, s) : Plane) = (sphereLoop s : Plane)
    change diskBoundaryPoint 0 s = (sphereLoop s : Plane)
    simp [diskBoundaryPoint]
  · -- H (1, s) = base
    intro s
    have hmem : (diskNullhomotopy (1, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskBoundaryPoint 1 s ∈ _
      simp only [diskBoundaryPoint, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
      exact sphereBasePoint.2
    apply Subtype.ext
    change (ρ (diskNullhomotopy (1, s)) : Plane) = (sphereBasePoint : Plane)
    rw [hid _ hmem]
    show (diskNullhomotopy (1, s) : Plane) = (sphereBasePoint : Plane)
    change diskBoundaryPoint 1 s = (sphereBasePoint : Plane)
    simp [diskBoundaryPoint]
  · -- rel endpoints: for s ∈ {0,1}, H t s = sphereLoop s = base
    intro t s hs
    have hs' : (sphereLoop s : Plane) = (sphereBasePoint : Plane) := by
      rcases hs with h | h
      · rw [show s = (0 : I) from h, sphereLoop_zero]
      · rw [show s = (1 : I) from h, sphereLoop_one]
    have hmem : (diskNullhomotopy (t, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskBoundaryPoint t s ∈ _
      simp only [diskBoundaryPoint, hs', ← add_smul, sub_add_cancel, one_smul]
      exact sphereBasePoint.2
    apply Subtype.ext
    change (ρ (diskNullhomotopy (t, s)) : Plane) = (sphereLoop s : Plane)
    rw [hid _ hmem, hs']
    show (diskNullhomotopy (t, s) : Plane) = (sphereBasePoint : Plane)
    change diskBoundaryPoint t s = (sphereBasePoint : Plane)
    simp only [diskBoundaryPoint, hs', ← add_smul, sub_add_cancel, one_smul]

/-! ## Phase 3 — Brouwer for the closed unit disk

Given a fixed-point-free self-map `f` of the disk, the ray from `f x` through `x`
exits the boundary circle at a point `ρ x`; this `ρ` is a retraction, forbidden
by Phase 2. -/

section Disk

variable (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))

/-- **Math.** The direction vector `x - f x` of the ray. -/
noncomputable def displacement (x : closedBall (0 : Plane) 1) : Plane := (x : Plane) - (f x : Plane)

/-- **Math.** Quadratic coefficient `A = ‖x - f x‖²`. -/
noncomputable def raySphereQuadA (x : closedBall (0 : Plane) 1) : ℝ :=
  ⟪displacement f x, displacement f x⟫
/-- **Math.** Coefficient `B = ⟪f x, x - f x⟫`. -/
noncomputable def raySphereQuadB (x : closedBall (0 : Plane) 1) : ℝ :=
  ⟪(f x : Plane), displacement f x⟫
/-- **Math.** Coefficient `C = ‖f x‖² - 1 ≤ 0`. -/
noncomputable def raySphereQuadC (x : closedBall (0 : Plane) 1) : ℝ := ‖(f x : Plane)‖ ^ 2 - 1
/-- **Math.** Discriminant `B² - A·C ≥ 0`. -/
noncomputable def raySphereDiscriminant (x : closedBall (0 : Plane) 1) : ℝ :=
  (raySphereQuadB f x) ^ 2 - raySphereQuadA f x * raySphereQuadC f x
/-- **Math.** The (larger) root parameter `t = (-B + √disc)/A`. -/
noncomputable def raySphereRoot (x : closedBall (0 : Plane) 1) : ℝ :=
  (- raySphereQuadB f x + Real.sqrt (raySphereDiscriminant f x)) / raySphereQuadA f x
/-- **Math.** The exit point `ρ x = f x + t·(x - f x)` on the boundary circle. -/
noncomputable def retractionPoint (x : closedBall (0 : Plane) 1) : Plane :=
  (f x : Plane) + raySphereRoot f x • displacement f x

lemma raySphereQuadC_nonpos (x) : raySphereQuadC f x ≤ 0 := by
  rw [raySphereQuadC, sub_nonpos]
  have : ‖(f x : Plane)‖ ≤ 1 := by
    have := (f x).2; rw [mem_closedBall, dist_zero_right] at this; exact this
  nlinarith [norm_nonneg (f x : Plane)]


lemma continuous_fval : Continuous fun x : closedBall (0 : Plane) 1 => (f x : Plane) :=
  continuous_subtype_val.comp (map_continuous f)


lemma continuous_displacement : Continuous (displacement f) :=
  continuous_subtype_val.sub (continuous_fval f)


lemma continuous_raySphereQuadA : Continuous (raySphereQuadA f) :=
  (continuous_displacement f).inner (continuous_displacement f)


lemma continuous_raySphereQuadB : Continuous (raySphereQuadB f) :=
  (continuous_fval f).inner (continuous_displacement f)


lemma continuous_raySphereQuadC : Continuous (raySphereQuadC f) :=
  ((continuous_fval f).norm.pow 2).sub continuous_const


lemma continuous_raySphereDiscriminant : Continuous (raySphereDiscriminant f) :=
  ((continuous_raySphereQuadB f).pow 2).sub
    ((continuous_raySphereQuadA f).mul (continuous_raySphereQuadC f))


variable (hf : ∀ x, (f x : Plane) ≠ (x : Plane))
include hf

lemma displacement_ne (x) : displacement f x ≠ 0 := by
  simp only [displacement, sub_ne_zero]; exact fun h => hf x h.symm


lemma raySphereQuadA_pos (x) : 0 < raySphereQuadA f x := by
  rw [raySphereQuadA, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (displacement_ne f hf x)) 2


lemma raySphereDiscriminant_nonneg (x) : 0 ≤ raySphereDiscriminant f x := by
  have hA := (raySphereQuadA_pos f hf x).le
  have hC := raySphereQuadC_nonpos f x
  have : 0 ≤ raySphereQuadA f x * (- raySphereQuadC f x) := mul_nonneg hA (by linarith)
  rw [raySphereDiscriminant]; nlinarith [sq_nonneg (raySphereQuadB f x)]


/-- **Math.** The exit point lies on the unit circle. -/
lemma norm_retractionPoint (x) : ‖retractionPoint f x‖ = 1 := by
  have hA := raySphereQuadA_pos f hf x
  have hsq : (Real.sqrt (raySphereDiscriminant f x)) ^ 2 = raySphereDiscriminant f x :=
    Real.sq_sqrt (raySphereDiscriminant_nonneg f hf x)
  have hnormsq : ‖retractionPoint f x‖ ^ 2 = 1 := by
    rw [retractionPoint, norm_add_sq_real, norm_smul, real_inner_smul_right]
    have hAe : ⟪displacement f x, displacement f x⟫ = raySphereQuadA f x := rfl
    have hBe : ⟪(f x : Plane), displacement f x⟫ = raySphereQuadB f x := rfl
    have hCe : ‖(f x : Plane)‖ ^ 2 = raySphereQuadC f x + 1 := by rw [raySphereQuadC]; ring
    rw [hBe, hCe]
    have hnd : ‖displacement f x‖ ^ 2 = raySphereQuadA f x := by
      rw [← real_inner_self_eq_norm_sq]; rfl
    rw [Real.norm_eq_abs, mul_pow, sq_abs, hnd]
    -- Now: (C+1) + 2*(t*B) + t^2 * A = 1, with t = (-B+√disc)/A
    rw [raySphereRoot]
    field_simp
    rw [raySphereDiscriminant] at hsq ⊢
    nlinarith [hsq, hA]
  have := norm_nonneg (retractionPoint f x)
  nlinarith [hnormsq, this]


/-- **Math.** On the boundary circle, `ρ` is the identity. -/
lemma retractionPoint_of_mem_sphere (x : closedBall (0 : Plane) 1)
    (hx : (x : Plane) ∈ sphere (0 : Plane) 1) :
    retractionPoint f x = (x : Plane) := by
  have hxn : ‖(x : Plane)‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hx
  have hA := raySphereQuadA_pos f hf x
  have eA : raySphereQuadA f x = ‖displacement f x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have eC : raySphereQuadC f x = ‖(f x : Plane)‖ ^ 2 - 1 := rfl
  have hAdd : displacement f x + (f x : Plane) = (x : Plane) := by rw [displacement]; abel
  have hcomm : ⟪displacement f x, (f x : Plane)⟫ = raySphereQuadB f x :=
    by rw [raySphereQuadB, real_inner_comm]
  have hexp : ‖(x : Plane)‖ ^ 2
      = ‖displacement f x‖ ^ 2 + 2 * ⟪displacement f x, (f x : Plane)⟫ + ‖(f x : Plane)‖ ^ 2 := by
    rw [← hAdd, norm_add_sq_real]
  rw [hxn, hcomm] at hexp
  -- A + 2B + C = 0
  have hkey : raySphereQuadA f x + 2 * raySphereQuadB f x + raySphereQuadC f x = 0 := by
    rw [eA, eC]; linear_combination -hexp
  -- A + B = ⟪x, x - f x⟫ = 1 - ⟪x, f x⟫ ≥ 0
  have hApB : raySphereQuadA f x + raySphereQuadB f x = ⟪(x : Plane), displacement f x⟫ := by
    rw [raySphereQuadA, raySphereQuadB, ← inner_add_left, hAdd]
  have hxd : ⟪(x : Plane), displacement f x⟫ = 1 - ⟪(x : Plane), (f x : Plane)⟫ := by
    rw [displacement, inner_sub_right, real_inner_self_eq_norm_sq, hxn]; norm_num
  have hcs : ⟪(x : Plane), (f x : Plane)⟫ ≤ 1 := by
    have hfn : ‖(f x : Plane)‖ ≤ 1 := by
      have := (f x).2; rwa [mem_closedBall, dist_zero_right] at this
    calc ⟪(x : Plane), (f x : Plane)⟫ ≤ ‖(x : Plane)‖ * ‖(f x : Plane)‖ := real_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [hxn]; exact mul_le_mul le_rfl hfn (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hAB : 0 ≤ raySphereQuadA f x + raySphereQuadB f x := by rw [hApB, hxd]; linarith
  -- disc = (A+B)², so √disc = A+B, t = 1
  have hdisc : raySphereDiscriminant f x = (raySphereQuadA f x + raySphereQuadB f x) ^ 2 := by
    rw [raySphereDiscriminant]; linear_combination (-raySphereQuadA f x) * hkey
  have hsqrt : Real.sqrt (raySphereDiscriminant f x) = raySphereQuadA f x + raySphereQuadB f x := by
    rw [hdisc, Real.sqrt_sq hAB]
  have ht1 : raySphereRoot f x = 1 := by
    have hnum :
        -raySphereQuadB f x + (raySphereQuadA f x + raySphereQuadB f x)
          = raySphereQuadA f x :=
      by ring
    rw [raySphereRoot, hsqrt, hnum, div_self hA.ne']
  rw [retractionPoint, ht1, one_smul, displacement]; abel

/-! ### Continuity of the retraction -/


lemma continuous_raySphereRoot : Continuous (raySphereRoot f) :=
  Continuous.div (((continuous_raySphereQuadB f).neg).add (continuous_raySphereDiscriminant f).sqrt)
    (continuous_raySphereQuadA f) (fun x => (raySphereQuadA_pos f hf x).ne')


lemma continuous_retractionPoint : Continuous (retractionPoint f) :=
  (continuous_fval f).add ((continuous_raySphereRoot f hf).smul (continuous_displacement f))

end Disk

/-- **Math.** **Phase 3.** Brouwer's fixed point theorem for the closed unit disk. -/
theorem brouwer_disk (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1)) :
    ∃ x, f x = x := by
  by_contra hcon
  push Not at hcon
  have hf : ∀ x, (f x : Plane) ≠ (x : Plane) := fun x h => hcon x (Subtype.ext h)
  have hρmem : ∀ x, retractionPoint f x ∈ closedBall (0 : Plane) 1 := fun x => by
    rw [mem_closedBall, dist_zero_right, norm_retractionPoint f hf x]
  refine no_retraction ⟨fun x => ⟨retractionPoint f x, hρmem x⟩,
    (continuous_retractionPoint f hf).subtype_mk _⟩
    (fun x => ?_) (fun x hx => ?_)
  · change retractionPoint f x ∈ sphere (0 : Plane) 1
    rw [mem_sphere_zero_iff_norm]; exact norm_retractionPoint f hf x
  · change retractionPoint f x = (x : Plane)
    exact retractionPoint_of_mem_sphere f hf x hx

/-! ## Phase 4 — general nonempty compact convex sets -/

/-- **Eng.** Transfer of the fixed-point property along a homeomorphism. -/
theorem fixedPoint_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (hY : ∀ g : C(Y, Y), ∃ y, g y = y) (f : C(X, X)) : ∃ x, f x = x := by
  obtain ⟨y, hy⟩ := hY ((⟨φ, φ.continuous⟩ : C(X, Y)).comp
      (f.comp (⟨φ.symm, φ.symm.continuous⟩ : C(Y, X))))
  refine ⟨φ.symm y, ?_⟩
  have hfy : φ (f (φ.symm y)) = y := hy
  calc f (φ.symm y) = φ.symm (φ (f (φ.symm y))) := (φ.symm_apply_apply _).symm
    _ = φ.symm y := by rw [hfy]

/-! ### Brouwer on an arbitrary closed ball (by rescaling) -/

/-- **Eng.** Rescaling homeomorphism `closedBall 0 R ≃ₜ closedBall 0 1` (`x ↦ R⁻¹ • x`). -/
noncomputable def ballRescale (R : ℝ) (hR : 0 < R) :
    closedBall (0 : Plane) R ≃ₜ closedBall (0 : Plane) 1 where
  toFun x := ⟨R⁻¹ • (x : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hx : ‖(x : Plane)‖ ≤ R := by have := x.2; rwa [mem_closedBall, dist_zero_right] at this
    rw [inv_mul_le_iff₀ hR]; simpa using hx⟩
  invFun y := ⟨R • (y : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hy : ‖(y : Plane)‖ ≤ 1 := by have := y.2; rwa [mem_closedBall, dist_zero_right] at this
    nlinarith [norm_nonneg (y : Plane)]⟩
  left_inv x := by ext; simp [smul_smul, mul_inv_cancel₀ hR.ne']
  right_inv y := by ext; simp [smul_smul, inv_mul_cancel₀ hR.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Eng.** **Brouwer for a closed ball of arbitrary positive radius.** -/
theorem brouwer_ball (R : ℝ) (hR : 0 < R)
    (f : C(closedBall (0 : Plane) R, closedBall (0 : Plane) R)) : ∃ x, f x = x :=
  fixedPoint_of_homeo (ballRescale R hR) (fun g => brouwer_disk g) f

/-! ### Nearest-point projection onto a nonempty compact convex set

Any nonempty compact convex set `s ⊆ ℝ²` is a retract of any closed ball
containing it, via the (nonexpansive, hence continuous) nearest-point
projection.  This yields Brouwer for all such `s` uniformly — in particular the
degenerate empty-interior case is handled without any dimension reduction. -/

section Projection

variable {s : Set Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)

/-- **Eng.** Nearest-point projection of `u` onto the nonempty compact convex set `s`. -/
noncomputable def nearestPointProjection (u : Plane) : Plane :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose

lemma nearestPointProjection_mem (u : Plane) : nearestPointProjection hconv hcomp hne u ∈ s :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.1

/-- **Eng.** The variational characterization of the projection. -/
lemma nearestPointProjection_inner_le (u : Plane) {w : Plane} (hw : w ∈ s) :
    ⟪u - nearestPointProjection hconv hcomp hne u,
      w - nearestPointProjection hconv hcomp hne u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (nearestPointProjection_mem hconv hcomp hne u)).mp
    (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.2 w hw

/-- **Eng.** The projection fixes the points of `s`. -/
lemma nearestPointProjection_eq_self {u : Plane} (hu : u ∈ s) :
    nearestPointProjection hconv hcomp hne u = u :=
  by
  have h := nearestPointProjection_inner_le hconv hcomp hne u hu
  rw [real_inner_self_eq_norm_sq] at h
  have hz : u - nearestPointProjection hconv hcomp hne u = 0 := by
    have hn := norm_nonneg (u - nearestPointProjection hconv hcomp hne u)
    have : ‖u - nearestPointProjection hconv hcomp hne u‖ = 0 := by nlinarith
    rwa [norm_eq_zero] at this
  rw [sub_eq_zero] at hz; exact hz.symm

/-- **Eng.** The projection is nonexpansive. -/
lemma nearestPointProjection_dist_le (u₁ u₂ : Plane) :
    ‖nearestPointProjection hconv hcomp hne u₁
        - nearestPointProjection hconv hcomp hne u₂‖ ≤ ‖u₁ - u₂‖ :=
      by
  set v₁ := nearestPointProjection hconv hcomp hne u₁
  set v₂ := nearestPointProjection hconv hcomp hne u₂
  have hb1 : 0 ≤ ⟪u₁ - v₁, v₁ - v₂⟫ := by
    have h :=
      nearestPointProjection_inner_le hconv hcomp hne u₁
        (nearestPointProjection_mem hconv hcomp hne u₂)
    rw [show v₂ - v₁ = -(v₁ - v₂) by abel, inner_neg_right] at h
    linarith
  have hb2 : ⟪u₂ - v₂, v₁ - v₂⟫ ≤ 0 :=
    nearestPointProjection_inner_le hconv hcomp hne u₂
      (nearestPointProjection_mem hconv hcomp hne u₁)
  have decomp : ⟪u₁ - u₂, v₁ - v₂⟫
      = ⟪u₁ - v₁, v₁ - v₂⟫ - ⟪u₂ - v₂, v₁ - v₂⟫ + ⟪v₁ - v₂, v₁ - v₂⟫ := by
    have hsum : u₁ - u₂ = (u₁ - v₁ - (u₂ - v₂)) + (v₁ - v₂) := by abel
    rw [← inner_sub_left, ← inner_add_left, ← hsum]
  have key : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫ := by
    rw [decomp, ← real_inner_self_eq_norm_sq]; linarith
  have hcs : ⟪u₁ - u₂, v₁ - v₂⟫ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have hsq : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by
      rw [← pow_two]; exact le_trans key hcs
    exact le_of_mul_le_mul_right hsq hpos

lemma continuous_nearestPointProjection : Continuous (nearestPointProjection hconv hcomp hne) :=
  (LipschitzWith.mk_one (fun u₁ u₂ => by
    rw [dist_eq_norm,
      dist_eq_norm]; exact nearestPointProjection_dist_le hconv hcomp hne u₁ u₂)).continuous

end Projection

/-- **The 2D Brouwer fixed point theorem.** Every continuous self-map of a
nonempty compact convex subset of `ℝ²` has a fixed point.  This matches the
`JordanCurve.BrouwerFPT` interface used to discharge the Jordan curve theorem.

The set `s` is contained in a closed ball `closedBall 0 R`; the nearest-point
projection `r : closedBall 0 R → s` is a continuous retraction, so the self-map
`incl ∘ f ∘ r` of the ball has (by `brouwer_ball`) a fixed point `x`, whose
coordinates lie in `s`, whence `r x` is a fixed point of `f`. -/
theorem brouwerFPT : ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x := by
  intro s hconv hcomp hne f
  obtain ⟨R, hR, hsub⟩ := hcomp.isBounded.subset_closedBall_lt 0 0
  let incl : C(s, closedBall (0 : Plane) R) :=
    ⟨fun y => ⟨(y : Plane), hsub y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C(closedBall (0 : Plane) R, s) :=
    ⟨fun x => ⟨nearestPointProjection hconv hcomp hne (x : Plane),
      nearestPointProjection_mem hconv hcomp hne (x : Plane)⟩,
      ((continuous_nearestPointProjection hconv hcomp hne).comp
        continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := brouwer_ball R hR (incl.comp (f.comp r))
  refine ⟨r x, ?_⟩
  apply Subtype.ext
  have hval : (f (r x) : Plane) = (x : Plane) := congrArg Subtype.val hx
  have hxs : (x : Plane) ∈ s := by rw [← hval]; exact (f (r x)).2
  have hrx : ((r x : s) : Plane) = (x : Plane) := nearestPointProjection_eq_self hconv hcomp hne hxs
  change (f (r x) : Plane) = ((r x : s) : Plane)
  rw [hval, hrx]

end JordanCurve.Brouwer
