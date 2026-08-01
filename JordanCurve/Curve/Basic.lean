/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import JordanCurve.Crossing

/-!
# A Jordan curve and the topology of its complement

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-! ### Foundational topology of a Jordan curve `J = range r`

A Jordan curve is `J = range r` for `r : S¹ → ℝ²` continuous and injective. Here we
collect the purely topological facts about `J` and its complement that Maehara's
argument needs, independent of Brouwer:

* `J` is compact and closed, its complement `Jᶜ` is open (tasks 1-2);
* `r` is a (closed) embedding, so `J ≃ₜ S¹` (task 3);
* `Jᶜ` has exactly one unbounded connected component (PRELIM (a));
* each connected component of `Jᶜ` is open and path-connected (PRELIM (b)).
-/

/-- **Math.** The plane has rank `2 > 1`; the engine for connectivity of ball-complements. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  have h : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  rw [h]; norm_num

/-- **Math.** The exterior `{x | R < ‖x‖}` of a closed ball is connected in the plane
(dimension `2 > 1`). Proved as the continuous image of the connected set
`sphere 0 1 ×ˢ Ioi R` under `(s, t) ↦ t • s`. -/
theorem isConnected_compl_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {x : Plane | R < ‖x‖} := by
  have hconn : IsConnected ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) :=
    (isConnected_sphere one_lt_rank_plane 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have hset : {x : Plane | R < ‖x‖}
      = (fun p : Plane × ℝ => p.2 • p.1) '' ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) := by
    ext x
    simp only [mem_setOf_eq, mem_image, mem_prod, mem_Ioi, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR ht)]
      exact ht
  rw [hset]; exact himg

section JordanCurveData

variable (r : sphere (0 : Plane) 1 → Plane)

/-- **Math.** **Task 1.** The Jordan curve `J = range r` is compact (continuous image of the
compact circle `S¹`). -/
theorem jordanCurve_isCompact (hcont : Continuous r) : IsCompact (range r) :=
  isCompact_range hcont

/-- **Math.** **Task 1.** The Jordan curve `J = range r` is closed (compact in a Hausdorff
space). -/
theorem jordanCurve_isClosed (hcont : Continuous r) : IsClosed (range r) :=
  (jordanCurve_isCompact r hcont).isClosed

/-- **Math.** **Task 2.** The complement of the Jordan curve is open. -/
theorem isOpen_compl_jordanCurve (hcont : Continuous r) : IsOpen (range r)ᶜ :=
  (jordanCurve_isClosed r hcont).isOpen_compl

/-- **Math.** **Task 3.** A continuous injection of the compact circle into the plane is a
closed embedding. -/
theorem r_isClosedEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

/-- **Math.** **Task 3.** `r` is a topological embedding. -/
theorem r_isEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsEmbedding r :=
  (r_isClosedEmbedding r hcont hinj).isEmbedding

/-- **Math.** **Task 3.** The Jordan curve `J = range r` is homeomorphic to the circle `S¹`. -/
noncomputable def jordanCurveHomeo (hcont : Continuous r) (hinj : Injective r) :
    sphere (0 : Plane) 1 ≃ₜ (range r) :=
  (r_isEmbedding r hcont hinj).toHomeomorph

/-- **Math.** A radius `R ≥ 0` with `range r ⊆ closedBall 0 R` (compact ⇒ bounded). -/
private theorem exists_jordanCurve_bound (hcont : Continuous r) :
    ∃ R : ℝ, 0 ≤ R ∧ range r ⊆ closedBall (0 : Plane) R := by
  obtain ⟨R, hR⟩ := (jordanCurve_isCompact r hcont).isBounded.subset_closedBall 0
  exact ⟨max R 0, le_max_right R 0,
    hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩

/-- **Math.** **PRELIM (a).** `Jᶜ` has an unbounded connected component: pick any point in the
cobounded exterior `{x | R < ‖x‖}` of a ball containing `J`; that exterior is
connected, lies in `Jᶜ`, and is unbounded, so the component containing it is
unbounded. -/
theorem exists_unbounded_component (hcont : Continuous r) :
    ∃ x ∈ (range r)ᶜ, ¬ IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  have hEconn : IsConnected {z : Plane | R < ‖z‖} := isConnected_compl_closedBall hR0
  have hEsub : {z : Plane | R < ‖z‖} ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  have hEnb : ¬ IsBounded {z : Plane | R < ‖z‖} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    obtain ⟨z, hz⟩ := NormedSpace.exists_lt_norm ℝ Plane (max M R)
    have hzE : z ∈ {z : Plane | R < ‖z‖} := lt_of_le_of_lt (le_max_right M R) hz
    have hzM := hM hzE
    rw [mem_closedBall_zero_iff] at hzM
    exact absurd (le_max_left M R) (not_le.2 (lt_of_lt_of_le hz hzM))
  obtain ⟨x, hxE⟩ := hEconn.nonempty
  refine ⟨x, hEsub hxE, ?_⟩
  have hEcomp : {z : Plane | R < ‖z‖} ⊆ connectedComponentIn (range r)ᶜ x :=
    hEconn.isPreconnected.subset_connectedComponentIn hxE hEsub
  exact fun hbdd => hEnb (hbdd.subset hEcomp)

/-- **Math.** **PRELIM (a).** Any two unbounded components of `Jᶜ` coincide: each unbounded
component must meet the connected cobounded exterior `{x | R < ‖x‖}`, which therefore
lies in a single component. -/
theorem unbounded_component_unique (hcont : Continuous r) {x y : Plane}
    (hxu : ¬ IsBounded (connectedComponentIn (range r)ᶜ x))
    (hyu : ¬ IsBounded (connectedComponentIn (range r)ᶜ y)) :
    connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  set E : Set Plane := {z : Plane | R < ‖z‖} with hE
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  -- An unbounded component meets `E`.
  have meetsE : ∀ z : Plane,
      ¬ IsBounded (connectedComponentIn (range r)ᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn (range r)ᶜ z := by
    intro z hz
    by_contra hcon
    push Not at hcon
    apply hz
    have hsubBall : connectedComponentIn (range r)ᶜ z ⊆ closedBall (0 : Plane) R := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hEcomp : E ⊆ connectedComponentIn (range r)ᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub
  -- Both components equal the component of `p`.
  obtain ⟨wx, hwxE, hwxc⟩ := meetsE x hxu
  obtain ⟨wy, hwyE, hwyc⟩ := meetsE y hyu
  have hx : connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwxc, ← connectedComponentIn_eq (hEcomp hwxE)]
  have hy : connectedComponentIn (range r)ᶜ y = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwyc, ← connectedComponentIn_eq (hEcomp hwyE)]
  rw [hx, hy]

/-- **Math.** **PRELIM (b).** Each connected component of `Jᶜ` is open (`Jᶜ` is open and the
plane is locally connected). -/
theorem isOpen_component (hcont : Continuous r) (x : Plane) :
    IsOpen (connectedComponentIn (range r)ᶜ x) :=
  (isOpen_compl_jordanCurve r hcont).connectedComponentIn

/-- **Math.** **PRELIM (b).** Each connected component of `Jᶜ` is path-connected (it is open
and connected in the locally path-connected plane). -/
theorem isPathConnected_component (hcont : Continuous r) {x : Plane}
    (hx : x ∈ (range r)ᶜ) :
    IsPathConnected (connectedComponentIn (range r)ᶜ x) :=
  ((isOpen_component r hcont x).isConnected_iff_isPathConnected).mp
    (isConnected_connectedComponentIn_iff.mpr hx)

end JordanCurveData

end JordanCurve
