/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UnitInterval

/-!
# Arc scaffolding for the (continuous) Jordan curve theorem

Reusable topology lemmas that split a topological circle into closed arcs, each
homeomorphic to the unit interval.  These feed Maehara's proof of the Jordan
curve theorem.

`Plane := EuclideanSpace ℝ (Fin 2)` and the circle is `Metric.sphere (0:Plane) 1`.

Main deliverables:
* `circleHomeoSphere` / `spherePlaneHomeoCircle` — the bridge between Mathlib's
  `Circle` (unit circle in `ℂ`) and `sphere (0:Plane) 1`.
* `circleParam` — the angle parametrization `ℝ → sphere (0:Plane) 1`, continuous,
  `2π`-periodic, with explicit fibers and surjective.
* `arcHomeoUnitInterval` — a closed arc `circleParam '' Icc a b` (with `a < b`,
  `b - a < 2π`) is homeomorphic to `unitInterval`.
* `sphere_split` — two distinct points cut the circle into two closed arcs, each
  `≃ₜ unitInterval`, with union the whole circle and intersection the two points.
* `jordanCurve_split` — transport of `sphere_split` across a homeomorphism
  `sphere (0:Plane) 1 ≃ₜ K`.
* `exists_proper_arc` — a proper closed subset of the circle sits inside a proper
  closed arc `≃ₜ unitInterval`.
-/

@[expose] public section

namespace JordanCurve.Arcs

open Metric Set Function Real

/-- **Math.** The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## 1. The circle model bridge -/

/-- **Eng.** A linear isometry equivalence `ℂ ≃ₗᵢ[ℝ] Plane`, from the standard orthonormal
basis of `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def complexToPlaneIsometry : ℂ ≃ₗᵢ[ℝ] Plane :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- **Eng.** The underlying `Equiv` between Mathlib's `Circle` and the unit sphere of the
plane, induced by `complexToPlaneIsometry`. -/
noncomputable def circleEquivSphere : Circle ≃ sphere (0 : Plane) 1 where
  toFun z := ⟨complexToPlaneIsometry z, by
    rw [mem_sphere_zero_iff_norm, complexToPlaneIsometry.norm_map]; exact z.norm_coe⟩
  invFun w := ⟨complexToPlaneIsometry.symm w, by
    change complexToPlaneIsometry.symm w ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, complexToPlaneIsometry.symm.norm_map, ← mem_sphere_zero_iff_norm]
    exact w.2⟩
  left_inv z := by ext; simp [complexToPlaneIsometry.symm_apply_apply]
  right_inv w := by ext; simp [complexToPlaneIsometry.apply_symm_apply]

/-- **Eng.** **Circle model bridge.** `Circle ≃ₜ sphere (0:Plane) 1`. -/
noncomputable def circleHomeoSphere : Circle ≃ₜ sphere (0 : Plane) 1 :=
  Continuous.homeoOfEquivCompactToT2 (f := circleEquivSphere) <| by
    apply Continuous.subtype_mk
    exact complexToPlaneIsometry.continuous.comp continuous_subtype_val

/-- **Eng.** **Circle model bridge** (as requested): `sphere (0:Plane) 1 ≃ₜ Circle`. -/
noncomputable def spherePlaneHomeoCircle : sphere (0 : Plane) 1 ≃ₜ Circle :=
  circleHomeoSphere.symm

@[simp] lemma circleHomeoSphere_coe (z : Circle) :
    (circleHomeoSphere z : Plane) = complexToPlaneIsometry z := rfl

/-! ## 2. The angle parametrization -/

/-- **Math.** The angle parametrization `ℝ → sphere (0:Plane) 1`, `θ ↦` the plane point at
angle `θ` on the unit circle. -/
noncomputable def circleParam (θ : ℝ) : sphere (0 : Plane) 1 := circleHomeoSphere (Circle.exp θ)

@[continuity, fun_prop]
lemma continuous_circleParam : Continuous circleParam :=
  circleHomeoSphere.continuous.comp Circle.exp.continuous

/-- **Math.** Two angles give the same point iff they differ by an integer multiple of `2π`. -/
lemma circleParam_eq_iff {s t : ℝ} : circleParam s = circleParam t ↔ ∃ m : ℤ, s = t + m * (2 * π) :=
  by
  unfold circleParam
  rw [circleHomeoSphere.injective.eq_iff, Circle.exp_eq_exp]

/-- **Math.** The parametrization is surjective. -/
lemma circleParam_surjective : Surjective circleParam :=
  circleHomeoSphere.surjective.comp Circle.exp_surjective

/-- **Math.** The parametrization is `2π`-periodic. -/
lemma circleParam_periodic : Function.Periodic circleParam (2 * π) := by
  intro θ
  rw [circleParam_eq_iff]
  exact ⟨1, by push_cast; ring⟩

/-! ## 2. Closed arc ≃ₜ unitInterval -/

/-- **Math.** On a closed interval shorter than a full turn, `circleParam` is injective. -/
lemma circleParam_injOn {a b : ℝ} (h : b - a < 2 * π) : InjOn circleParam (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨m, hm⟩ := circleParam_eq_iff.1 hst
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨hαs, hsβ⟩ := hs
  obtain ⟨hat, htb⟩ := ht
  have e : s - t = (m : ℝ) * (2 * π) := by linarith
  have hlt : (m : ℝ) * (2 * π) < 1 * (2 * π) := by rw [one_mul, ← e]; linarith
  have hgt : (-1 : ℝ) * (2 * π) < (m : ℝ) * (2 * π) := by rw [neg_one_mul, ← e]; linarith
  have u1 : (m : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hp.le
  have u2 : (-1 : ℝ) < (m : ℝ) := lt_of_mul_lt_mul_right hgt hp.le
  have hm0 : m = 0 := by
    have b1 : m < (1 : ℤ) := by exact_mod_cast u1
    have b2 : (-1 : ℤ) < m := by exact_mod_cast u2
    omega
  rw [hm0] at hm; push_cast at hm; linarith

/-- **Math.** Image of a closed interval of angles under `circleParam` (a "closed arc"). -/
lemma isClosed_arc (a b : ℝ) : IsClosed (circleParam '' Icc a b) :=
  (isCompact_Icc.image continuous_circleParam).isClosed

/-- **Mixed.** On a short closed interval `circleParam` restricts to a homeomorphism onto its
image (the arc). -/
noncomputable def arcHomeoIcc {a b : ℝ} (h : b - a < 2 * π) :
    (Icc a b) ≃ₜ (circleParam '' Icc a b) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn circleParam (Icc a b) (circleParam_injOn h))
    (continuous_induced_rng.2 (continuous_circleParam.comp continuous_subtype_val))

/-- **Math.** **Closed arc ≃ₜ unitInterval.** A closed arc `circleParam '' Icc a b` with
`a < b` and `b - a < 2π` is homeomorphic to the unit interval. -/
noncomputable def arcHomeoUnitInterval {a b : ℝ} (hab : a < b) (h : b - a < 2 * π) :
    (circleParam '' Icc a b) ≃ₜ unitInterval :=
  (arcHomeoIcc h).symm.trans (iccHomeoI a b hab)

/-- **Eng.** The left endpoint `circleParam a` of the arc maps to `0` under
`arcHomeoUnitInterval`. -/
lemma arcHomeoUnitInterval_apply_left {a b : ℝ} (hab : a < b) (h : b - a < 2 * π)
    (hmem : circleParam a ∈ circleParam '' Icc a b) :
    arcHomeoUnitInterval hab h ⟨circleParam a, hmem⟩ = 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have key : (arcHomeoIcc h) ⟨a, ha⟩ = ⟨circleParam a, hmem⟩ := Subtype.ext rfl
  have hsymm : (arcHomeoIcc h).symm ⟨circleParam a, hmem⟩ = ⟨a, ha⟩ := by
    rw [← key, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change ((arcHomeoIcc h).symm.trans (iccHomeoI a b hab) ⟨circleParam a, hmem⟩ : ℝ)
      = ((0 : unitInterval) : ℝ)
  rw [Homeomorph.trans_apply, hsymm, iccHomeoI_apply_coe, Set.Icc.coe_zero]
  change (a - a) / (b - a) = 0
  rw [sub_self, zero_div]

/-- **Eng.** The right endpoint `circleParam b` of the arc maps to `1` under
`arcHomeoUnitInterval`. -/
lemma arcHomeoUnitInterval_apply_right {a b : ℝ} (hab : a < b) (h : b - a < 2 * π)
    (hmem : circleParam b ∈ circleParam '' Icc a b) :
    arcHomeoUnitInterval hab h ⟨circleParam b, hmem⟩ = 1 := by
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have key : (arcHomeoIcc h) ⟨b, hb⟩ = ⟨circleParam b, hmem⟩ := Subtype.ext rfl
  have hsymm : (arcHomeoIcc h).symm ⟨circleParam b, hmem⟩ = ⟨b, hb⟩ := by
    rw [← key, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  change ((arcHomeoIcc h).symm.trans (iccHomeoI a b hab) ⟨circleParam b, hmem⟩ : ℝ)
      = ((1 : unitInterval) : ℝ)
  rw [Homeomorph.trans_apply, hsymm, iccHomeoI_apply_coe, Set.Icc.coe_one]
  change (b - a) / (b - a) = 1
  rw [div_self (by linarith : b - a ≠ 0)]

/-! ## 2b. Interior of an arc is path-connected -/

/-- **Math.** **Interior of an arc is path-connected.** If `A ≃ₜ unitInterval` via `e` and two
points `x, y ∈ A` are the endpoints (`{e x, e y} = {0, 1}`), then `A \ {x, y}` — the
arc with its endpoints removed — is path-connected. -/
theorem arc_interior_isPathConnected {X : Type*} [TopologicalSpace X] {A : Set X}
    (e : A ≃ₜ unitInterval) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (he : ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) = {0, 1}) :
    IsPathConnected (A \ {x, y}) := by
  -- endpoint values, extracted from the set equality
  have hmx : e ⟨x, hx⟩ ∈ ({0, 1} : Set unitInterval) := by
    rw [← he]; exact Set.mem_insert _ _
  have hmy : e ⟨y, hy⟩ ∈ ({0, 1} : Set unitInterval) := by
    rw [← he]; exact Set.mem_insert_of_mem _ rfl
  have h0 : (0 : unitInterval) ∈ ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) := by
    rw [he]; exact Set.mem_insert _ _
  have h1 : (1 : unitInterval) ∈ ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) := by
    rw [he]; exact Set.mem_insert_of_mem _ rfl
  -- the parametrizing map from `Ioo 0 1 ⊆ ℝ`
  set g : ℝ → X := fun s => ((e.symm (Set.projIcc 0 1 (by norm_num) s) : A) : X) with hg
  have hgcont : Continuous g :=
    continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hIoo : IsPathConnected (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num⟩
  have himg : g '' Set.Ioo (0 : ℝ) 1 = A \ {x, y} := by
    ext p
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
      have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) s = ⟨s, hsI⟩ :=
        Set.projIcc_of_mem _ hsI
      refine ⟨(e.symm _).2, ?_⟩
      rintro (hgx | hgy)
      · -- g s = x is impossible
        have heq : e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) s) = ⟨x, hx⟩ :=
          Subtype.ext hgx
        have hval : Set.projIcc (0 : ℝ) 1 (by norm_num) s = e ⟨x, hx⟩ := by
          rw [← heq, Homeomorph.apply_symm_apply]
        rw [hproj] at hval
        rcases hmx with hxe | hxe
        · rw [hxe] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.1.ne')
        · rw [Set.mem_singleton_iff] at hxe; rw [hxe] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.2.ne)
      · -- g s = y is impossible
        have heq : e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) s) = ⟨y, hy⟩ :=
          Subtype.ext hgy
        have hval : Set.projIcc (0 : ℝ) 1 (by norm_num) s = e ⟨y, hy⟩ := by
          rw [← heq, Homeomorph.apply_symm_apply]
        rw [hproj] at hval
        rcases hmy with hye | hye
        · rw [hye] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.1.ne')
        · rw [Set.mem_singleton_iff] at hye; rw [hye] at hval
          exact absurd (congrArg Subtype.val hval) (by simpa using hs.2.ne)
    · rintro ⟨hpA, hpxy⟩
      have hpx : p ≠ x := fun h => hpxy (Or.inl h)
      have hpy : p ≠ y := fun h => hpxy (Or.inr h)
      set t : unitInterval := e ⟨p, hpA⟩ with ht
      have htne0 : t ≠ 0 := by
        intro h; apply hpx
        rcases h0 with h0e | h0e
        · have : e ⟨p, hpA⟩ = e ⟨x, hx⟩ := by rw [← ht, h, h0e]
          exact congrArg Subtype.val (e.injective this)
        · rw [Set.mem_singleton_iff] at h0e
          have : e ⟨p, hpA⟩ = e ⟨y, hy⟩ := by rw [← ht, h, h0e]
          exact absurd (congrArg Subtype.val (e.injective this)) hpy
      have htne1 : t ≠ 1 := by
        intro h; apply hpx
        rcases h1 with h1e | h1e
        · have : e ⟨p, hpA⟩ = e ⟨x, hx⟩ := by rw [← ht, h, h1e]
          exact congrArg Subtype.val (e.injective this)
        · rw [Set.mem_singleton_iff] at h1e
          have : e ⟨p, hpA⟩ = e ⟨y, hy⟩ := by rw [← ht, h, h1e]
          exact absurd (congrArg Subtype.val (e.injective this)) hpy
      have htmem : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        refine ⟨lt_of_le_of_ne t.2.1 ?_, lt_of_le_of_ne t.2.2 ?_⟩
        · intro h; exact htne0 (Subtype.ext h.symm)
        · intro h; exact htne1 (Subtype.ext h)
      refine ⟨(t : ℝ), htmem, ?_⟩
      have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ) = t :=
        Set.projIcc_val _ t
      change ((e.symm (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ)) : A) : X) = p
      rw [hproj, ht, Homeomorph.symm_apply_apply]
  rw [← himg]
  exact hIoo.image hgcont

/-- **Math.** **`arc_interior_joinedIn`.** For an arc `A ≃ₜ unitInterval` via `e` whose two
endpoints are `x, y` (`{e x, e y} = {0, 1}`), any two interior points `u, v ∈ A`
(neither equal to `x` nor `y`) are joined by a path inside `A \ {x, y}`. -/
theorem arc_interior_joinedIn {X : Type*} [TopologicalSpace X] {A : Set X}
    (e : A ≃ₜ unitInterval) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (he : ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) = {0, 1})
    {u v : X} (hu : u ∈ A) (hv : v ∈ A)
    (hux : u ∉ ({x, y} : Set X)) (hvx : v ∉ ({x, y} : Set X)) :
    JoinedIn (A \ {x, y}) u v :=
  (arc_interior_isPathConnected e hx hy he).joinedIn u ⟨hu, hux⟩ v ⟨hv, hvx⟩

/-! ## 3. The two-point split -/

/-- **Math.** **Two-point split.** Two distinct points `x`, `y` on the circle cut it into
two closed arcs `A₁`, `A₂`, each homeomorphic to the unit interval, whose union
is the whole circle and whose intersection is exactly `{x, y}`. -/
theorem sphere_split {x y : sphere (0 : Plane) 1} (hxy : x ≠ y) :
    ∃ A₁ A₂ : Set (sphere (0 : Plane) 1),
      IsClosed A₁ ∧ IsClosed A₂ ∧ A₁ ∪ A₂ = univ ∧ A₁ ∩ A₂ = {x, y} ∧
      Nonempty (A₁ ≃ₜ unitInterval) ∧ Nonempty (A₂ ≃ₜ unitInterval) ∧
      IsPathConnected (A₁ \ {x, y}) ∧ IsPathConnected (A₂ \ {x, y}) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨α, hα⟩ := circleParam_surjective x
  obtain ⟨β₀, hβ₀⟩ := circleParam_surjective y
  set β := toIocMod hp α β₀ with hβdef
  have hmemβ : β ∈ Ioc α (α + 2 * π) := toIocMod_mem_Ioc hp α β₀
  -- `circleParam β = y`
  have hpar_β : circleParam β = y := by
    have hz : β₀ - β = (toIocDiv hp α β₀ : ℤ) • (2 * π) := self_sub_toIocMod hp α β₀
    rw [zsmul_eq_mul] at hz
    have hpp : circleParam β = circleParam β₀ := by
      rw [circleParam_eq_iff]; exact ⟨-(toIocDiv hp α β₀), by push_cast; linarith⟩
    rw [hpp, hβ₀]
  -- `β < α + 2π` (else `y = x`)
  have hβlt : β < α + 2 * π := by
    rcases lt_or_eq_of_le hmemβ.2 with h | h
    · exact h
    · exact absurd (by rw [← hpar_β, h, circleParam_periodic, hα] : y = x).symm hxy
  have hlen1 : β - α < 2 * π := by linarith [hβlt]
  have hlen2 : (α + 2 * π) - β < 2 * π := by linarith [hmemβ.1]
  -- union is everything
  have hunion : (circleParam '' Icc α β) ∪ (circleParam '' Icc β (α + 2 * π)) = univ := by
    rw [← image_union, Icc_union_Icc_eq_Icc hmemβ.1.le hβlt.le,
      circleParam_periodic.image_Icc hp α, circleParam_surjective.range_eq]
  -- intersection is `{x, y}`
  have hinter : (circleParam '' Icc α β) ∩ (circleParam '' Icc β (α + 2 * π)) = {x, y} := by
    ext z
    simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
      have hst : circleParam s = circleParam t := hsz.trans htz.symm
      obtain ⟨m, hm⟩ := circleParam_eq_iff.1 hst
      obtain ⟨hαs, hsβ⟩ := hs
      obtain ⟨hβt, htα⟩ := ht
      have e : s - t = (m : ℝ) * (2 * π) := by linarith
      have hm_ub : (m : ℝ) ≤ 0 := by
        have h2 : (m : ℝ) * (2 * π) ≤ 0 * (2 * π) := by rw [zero_mul, ← e]; linarith
        exact le_of_mul_le_mul_right h2 hp
      have hm_lb : (-1 : ℝ) ≤ (m : ℝ) := by
        have h2 : (-1 : ℝ) * (2 * π) ≤ (m : ℝ) * (2 * π) := by
          rw [neg_one_mul, ← e]; linarith
        exact le_of_mul_le_mul_right h2 hp
      have hcase : m = 0 ∨ m = -1 := by
        have a0 : m ≤ (0 : ℤ) := by exact_mod_cast hm_ub
        have a1 : (-1 : ℤ) ≤ m := by exact_mod_cast hm_lb
        omega
      rcases hcase with h0 | h1
      · right
        have hst2 : s = t := by rw [h0] at hm; push_cast at hm; linarith
        have hsβeq : s = β := le_antisymm hsβ (by rw [hst2]; exact hβt)
        rw [← hsz, hsβeq]; exact hpar_β
      · left
        have hst2 : s = t - 2 * π := by rw [h1] at hm; push_cast at hm; linarith
        have hsαeq : s = α := le_antisymm (by rw [hst2]; linarith) hαs
        rw [← hsz, hsαeq]; exact hα
    · rintro (rfl | rfl)
      · exact ⟨⟨α, ⟨le_refl α, hmemβ.1.le⟩, hα⟩,
          ⟨α + 2 * π, ⟨hβlt.le, le_refl _⟩, by rw [circleParam_periodic]; exact hα⟩⟩
      · exact ⟨⟨β, ⟨hmemβ.1.le, le_refl β⟩, hpar_β⟩,
          ⟨β, ⟨le_refl β, hβlt.le⟩, hpar_β⟩⟩
  -- path-connectedness of the two arcs with their shared endpoints removed
  have hmem_α₁ : circleParam α ∈ circleParam '' Icc α β := ⟨α, left_mem_Icc.2 hmemβ.1.le, rfl⟩
  have hmem_β₁ : circleParam β ∈ circleParam '' Icc α β := ⟨β, right_mem_Icc.2 hmemβ.1.le, rfl⟩
  have hxA1 : x ∈ circleParam '' Icc α β := hα ▸ hmem_α₁
  have hyA1 : y ∈ circleParam '' Icc α β := hpar_β ▸ hmem_β₁
  have hpc1 : IsPathConnected (circleParam '' Icc α β \ {x, y}) := by
    refine arc_interior_isPathConnected (arcHomeoUnitInterval hmemβ.1 hlen1) hxA1 hyA1 ?_
    have hex : arcHomeoUnitInterval hmemβ.1 hlen1 ⟨x, hxA1⟩ = 0 := by
      rw [show (⟨x, hxA1⟩ : ↥(circleParam '' Icc α β)) = ⟨circleParam α, hmem_α₁⟩ from
        Subtype.ext hα.symm]
      exact arcHomeoUnitInterval_apply_left hmemβ.1 hlen1 hmem_α₁
    have hey : arcHomeoUnitInterval hmemβ.1 hlen1 ⟨y, hyA1⟩ = 1 := by
      rw [show (⟨y, hyA1⟩ : ↥(circleParam '' Icc α β)) = ⟨circleParam β, hmem_β₁⟩ from
        Subtype.ext hpar_β.symm]
      exact arcHomeoUnitInterval_apply_right hmemβ.1 hlen1 hmem_β₁
    rw [hex, hey]
  have hmem_β₂ : circleParam β ∈ circleParam '' Icc β (α + 2 * π) :=
    ⟨β, left_mem_Icc.2 hβlt.le, rfl⟩
  have hmem_α₂ : circleParam (α + 2 * π) ∈ circleParam '' Icc β (α + 2 * π) :=
    ⟨α + 2 * π, right_mem_Icc.2 hβlt.le, rfl⟩
  have hxeq : circleParam (α + 2 * π) = x := by rw [circleParam_periodic]; exact hα
  have hxA2 : x ∈ circleParam '' Icc β (α + 2 * π) := hxeq ▸ hmem_α₂
  have hyA2 : y ∈ circleParam '' Icc β (α + 2 * π) := hpar_β ▸ hmem_β₂
  have hpc2 : IsPathConnected (circleParam '' Icc β (α + 2 * π) \ {x, y}) := by
    refine arc_interior_isPathConnected (arcHomeoUnitInterval hβlt hlen2) hxA2 hyA2 ?_
    have hex : arcHomeoUnitInterval hβlt hlen2 ⟨x, hxA2⟩ = 1 := by
      rw [show
        (⟨x, hxA2⟩ : ↥(circleParam '' Icc β (α + 2 * π))) = ⟨circleParam (α + 2 * π), hmem_α₂⟩
        from Subtype.ext hxeq.symm]
      exact arcHomeoUnitInterval_apply_right hβlt hlen2 hmem_α₂
    have hey : arcHomeoUnitInterval hβlt hlen2 ⟨y, hyA2⟩ = 0 := by
      rw [show (⟨y, hyA2⟩ : ↥(circleParam '' Icc β (α + 2 * π))) = ⟨circleParam β, hmem_β₂⟩ from
        Subtype.ext hpar_β.symm]
      exact arcHomeoUnitInterval_apply_left hβlt hlen2 hmem_β₂
    rw [hex, hey]; exact Set.pair_comm 1 0
  exact ⟨circleParam '' Icc α β, circleParam '' Icc β (α + 2 * π),
    isClosed_arc α β, isClosed_arc β (α + 2 * π), hunion, hinter,
    ⟨arcHomeoUnitInterval hmemβ.1 hlen1⟩, ⟨arcHomeoUnitInterval hβlt hlen2⟩, hpc1, hpc2⟩

/-! ## 4. Transport across a homeomorphism to a Jordan curve -/

/-- **Math.** **Transport to a Jordan curve.** Given a homeomorphism `f` from the circle to
a space `K` and two distinct points, the images of the two arcs split `K` into two
closed arcs `≃ₜ unitInterval` meeting exactly at `{f x, f y}`. -/
theorem jordanCurve_split {K : Type*} [TopologicalSpace K]
    (f : sphere (0 : Plane) 1 ≃ₜ K) {x y : sphere (0 : Plane) 1} (hxy : x ≠ y) :
    ∃ A₁ A₂ : Set K,
      IsClosed A₁ ∧ IsClosed A₂ ∧ A₁ ∪ A₂ = univ ∧ A₁ ∩ A₂ = {f x, f y} ∧
      Nonempty (A₁ ≃ₜ unitInterval) ∧ Nonempty (A₂ ≃ₜ unitInterval) ∧
      IsPathConnected (A₁ \ {f x, f y}) ∧ IsPathConnected (A₂ \ {f x, f y}) := by
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpc1, hpc2⟩ := sphere_split hxy
  have himg1 : f '' (A₁ \ {x, y}) = f '' A₁ \ {f x, f y} := by
    rw [Set.image_sdiff f.injective, Set.image_insert_eq, Set.image_singleton]
  have himg2 : f '' (A₂ \ {x, y}) = f '' A₂ \ {f x, f y} := by
    rw [Set.image_sdiff f.injective, Set.image_insert_eq, Set.image_singleton]
  refine ⟨f '' A₁, f '' A₂, f.isClosedMap _ hc1, f.isClosedMap _ hc2, ?_, ?_,
    ⟨(f.image A₁).symm.trans e1⟩, ⟨(f.image A₂).symm.trans e2⟩,
    himg1 ▸ hpc1.image f.continuous, himg2 ▸ hpc2.image f.continuous⟩
  · rw [← image_union, hu, image_univ, f.surjective.range_eq]
  · rw [← Set.image_inter f.injective, hi, Set.image_insert_eq, Set.image_singleton]

/-! ## 5. A proper closed arc containing a proper closed set -/

/-- **Math.** **Proper arc containing a set.** A proper closed subset `C` of the circle is
contained in a proper closed arc `A` (homeomorphic to the unit interval). -/
theorem exists_proper_arc {C : Set (sphere (0 : Plane) 1)}
    (hC : IsClosed C) (hCne : C ≠ univ) :
    ∃ A : Set (sphere (0 : Plane) 1),
      C ⊆ A ∧ A ≠ univ ∧ IsClosed A ∧ Nonempty (A ≃ₜ unitInterval) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem C).1 hCne
  obtain ⟨γ, hγ⟩ := circleParam_surjective z
  have hopen : IsOpen (circleParam ⁻¹' Cᶜ) := hC.isOpen_compl.preimage continuous_circleParam
  have hmemγ : γ ∈ circleParam ⁻¹' Cᶜ := by rw [mem_preimage, hγ]; exact hz
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hopen γ hmemγ
  set δ := min (ε / 2) (π / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδπ : δ < π := lt_of_le_of_lt (min_le_right _ _) (by linarith [pi_pos])
  have hδε : δ ≤ ε := le_trans (min_le_left _ _) (by linarith)
  have hsub : Ioo (γ - δ) (γ + δ) ⊆ circleParam ⁻¹' Cᶜ := by
    intro w hw
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨hw1, hw2⟩ := hw
    constructor <;> linarith
  -- `z ∉ A`, so `A ≠ univ`
  have hzA : z ∉ circleParam '' Icc (γ + δ) (γ + 2 * π - δ) := by
    rintro ⟨θ, hθ, hθz⟩
    have hpe : circleParam θ = circleParam γ := by rw [hθz, hγ]
    obtain ⟨m, hm⟩ := circleParam_eq_iff.1 hpe
    obtain ⟨hθ1, hθ2⟩ := hθ
    have e : (m : ℝ) * (2 * π) = θ - γ := by linarith
    have hpos : (0 : ℝ) < (m : ℝ) * (2 * π) := by rw [e]; linarith
    have hlt : (m : ℝ) * (2 * π) < 2 * π := by rw [e]; linarith
    have m1 : (0 : ℝ) < (m : ℝ) :=
      lt_of_mul_lt_mul_right (by rw [zero_mul]; exact hpos) hp.le
    have m2 : (m : ℝ) < 1 :=
      lt_of_mul_lt_mul_right (by rw [one_mul]; exact hlt) hp.le
    have a0 : (0 : ℤ) < m := by exact_mod_cast m1
    have a1 : m < (1 : ℤ) := by exact_mod_cast m2
    omega
  refine ⟨circleParam '' Icc (γ + δ) (γ + 2 * π - δ), ?_,
    (Set.ne_univ_iff_exists_notMem _).2 ⟨z, hzA⟩, isClosed_arc _ _,
    ⟨arcHomeoUnitInterval (by linarith) (by linarith)⟩⟩
  -- `C ⊆ A`
  intro c hc
  obtain ⟨θc, hθc⟩ := circleParam_surjective c
  set θ' := toIcoMod hp (γ + δ) θc with hθ'def
  have hmem' : θ' ∈ Ico (γ + δ) (γ + δ + 2 * π) := toIcoMod_mem_Ico hp (γ + δ) θc
  have hpar' : circleParam θ' = c := by
    have hz2 : θc - θ' = (toIcoDiv hp (γ + δ) θc : ℤ) • (2 * π) :=
      self_sub_toIcoMod hp (γ + δ) θc
    rw [zsmul_eq_mul] at hz2
    have : circleParam θ' = circleParam θc := by
      rw [circleParam_eq_iff]; exact ⟨-(toIcoDiv hp (γ + δ) θc), by push_cast; linarith⟩
    rw [this, hθc]
  have hθ'ub : θ' ≤ γ + 2 * π - δ := by
    by_contra h
    rw [not_le] at h
    have hmem2 : θ' - 2 * π ∈ Ioo (γ - δ) (γ + δ) := by
      constructor
      · linarith
      · linarith [hmem'.2]
    have hpre : (θ' - 2 * π) ∈ circleParam ⁻¹' Cᶜ := hsub hmem2
    rw [mem_preimage] at hpre
    have hpc : circleParam (θ' - 2 * π) = c := by
      rw [show θ' = (θ' - 2 * π) + 2 * π by ring, circleParam_periodic] at hpar'
      exact hpar'
    rw [hpc] at hpre
    exact hpre hc
  exact ⟨θ', ⟨hmem'.1, hθ'ub⟩, hpar'⟩

end JordanCurve.Arcs
