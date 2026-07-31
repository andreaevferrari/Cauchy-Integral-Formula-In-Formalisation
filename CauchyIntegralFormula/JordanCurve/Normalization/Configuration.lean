/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import CauchyIntegralFormula.JordanCurve.Normalization.Frame

/-!
# Maehara's configuration

Everything Maehara's argument needs about a normalized Jordan curve, in one
object: the two arcs the curve splits into, the four distinguished points
where the vertical axis meets them, and the midpoint the argument starts
from.

The alternative is what this replaces — a nested existential of fifteen
conjuncts, destructured at the top of every proof that uses it into a spread
of loose hypotheses that then have to be threaded, one by one, into any lemma
extracted from that proof. A helper taking thirty-six arguments is not a
helper; it is the same proof with a different indentation.

The names say where each point is. Going down the vertical axis:

* `topOfNorthern` — the highest point of the whole curve on the axis, and it
  lies on the northern arc;
* `bottomOfNorthern` — the lowest point of the *northern* arc on the axis;
* `topOfSouthernBelow` — the highest point of the southern arc on the axis
  that is still at or below `bottomOfNorthern`;
* `bottomOfSouthern` — the lowest point of the southern arc on the axis;
* `midpoint` — halfway between `bottomOfNorthern` and `topOfSouthernBelow`,
  which is the point the argument shows lies in a bounded component.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Math.** Maehara's configuration for a normalized Jordan curve: the arc
decomposition, the four distinguished points on the vertical axis, and the
midpoint between the two innermost of them.

A curve is *normalized* when its farthest pair sits at `normalizedLeftEnd`
and `normalizedRightEnd`; `exists_maehara_configuration` produces this object
for any such curve. -/
structure MaeharaConfiguration (r : sphere (0 : Plane) 1 → Plane) where
  /-- The northern arc. -/
  northern : Set Plane
  /-- The southern arc. -/
  southern : Set Plane
  /-- The highest point of the curve on the vertical axis. -/
  topOfNorthern : Plane
  /-- The lowest point of the northern arc on the vertical axis. -/
  bottomOfNorthern : Plane
  /-- The highest point of the southern arc on the axis at or below
  `bottomOfNorthern`. -/
  topOfSouthernBelow : Plane
  /-- The lowest point of the southern arc on the vertical axis. -/
  bottomOfSouthern : Plane
  /-- The midpoint of `bottomOfNorthern` and `topOfSouthernBelow`. -/
  midpoint : Plane
  /-- The curve lies in the normalized rectangle: this is what "normalized"
  buys, and every later estimate is inside that box. -/
  subset_rectangle : Set.range r ⊆ normalizedRectangle
  /-- The two arcs cover the curve. -/
  union_eq : northern ∪ southern = Set.range r
  /-- They meet exactly at the two ends of the normalized diameter. -/
  inter_eq : northern ∩ southern = {normalizedLeftEnd, normalizedRightEnd}
  /-- The northern arc minus its endpoints is path-connected. -/
  isPathConnected_northern :
    IsPathConnected (northern \ {normalizedLeftEnd, normalizedRightEnd})
  /-- The southern arc minus its endpoints is path-connected. -/
  isPathConnected_southern :
    IsPathConnected (southern \ {normalizedLeftEnd, normalizedRightEnd})
  /-- Each arc joins the two ends of the diameter. -/
  joinedIn_northern : JoinedIn northern normalizedLeftEnd normalizedRightEnd
  /-- The same for the southern arc. -/
  joinedIn_southern : JoinedIn southern normalizedLeftEnd normalizedRightEnd
  /-- `topOfNorthern` lies on the northern arc, … -/
  topOfNorthern_mem : topOfNorthern ∈ northern
  /-- … on the axis, … -/
  topOfNorthern_coord_zero : topOfNorthern 0 = 0
  /-- … and no point of the curve on the axis is higher. -/
  topOfNorthern_max : ∀ w ∈ Set.range r, w 0 = 0 → w 1 ≤ topOfNorthern 1
  /-- `bottomOfNorthern` lies on the northern arc, … -/
  bottomOfNorthern_mem : bottomOfNorthern ∈ northern
  /-- … on the axis, … -/
  bottomOfNorthern_coord_zero : bottomOfNorthern 0 = 0
  /-- … and no point of the northern arc on the axis is lower. -/
  bottomOfNorthern_min : ∀ w ∈ northern, w 0 = 0 → bottomOfNorthern 1 ≤ w 1
  /-- `topOfSouthernBelow` lies on the southern arc, … -/
  topOfSouthernBelow_mem : topOfSouthernBelow ∈ southern
  /-- … on the axis, … -/
  topOfSouthernBelow_coord_zero : topOfSouthernBelow 0 = 0
  /-- … at or below `bottomOfNorthern`, … -/
  topOfSouthernBelow_le : topOfSouthernBelow 1 ≤ bottomOfNorthern 1
  /-- … and it is the highest such point. -/
  topOfSouthernBelow_max :
    ∀ w ∈ southern, w 0 = 0 → w 1 ≤ bottomOfNorthern 1 → w 1 ≤ topOfSouthernBelow 1
  /-- `bottomOfSouthern` lies on the southern arc, … -/
  bottomOfSouthern_mem : bottomOfSouthern ∈ southern
  /-- … on the axis, … -/
  bottomOfSouthern_coord_zero : bottomOfSouthern 0 = 0
  /-- … and no point of the southern arc on the axis is lower. -/
  bottomOfSouthern_min : ∀ w ∈ southern, w 0 = 0 → bottomOfSouthern 1 ≤ w 1
  /-- The midpoint is where the argument starts. -/
  midpoint_eq : midpoint = !₂[(0 : ℝ), (bottomOfNorthern 1 + topOfSouthernBelow 1) / 2]
  /-- The four points are ordered down the axis: `q ≤ p ≤ z₀ ≤ m ≤ l`. -/
  bottomOfNorthern_le_topOfNorthern : bottomOfNorthern 1 ≤ topOfNorthern 1
  /-- … -/
  bottomOfSouthern_le_topOfSouthernBelow : bottomOfSouthern 1 ≤ topOfSouthernBelow 1
  /-- … -/
  topOfSouthernBelow_le_midpoint : topOfSouthernBelow 1 ≤ midpoint 1
  /-- … -/
  midpoint_le_bottomOfNorthern : midpoint 1 ≤ bottomOfNorthern 1

/-- **Eng.** A point of the curve on the vertical axis is neither end of the
diameter, since those have first coordinate `±1`. -/
theorem not_mem_ends_of_coord_zero {w : Plane} (hw : w 0 = 0) :
    w ∉ ({normalizedLeftEnd, normalizedRightEnd} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h) <;>
    (have hc := congrArg (fun x : Plane => x 0) h; simp only [hw] at hc; norm_num at hc)

namespace MaeharaConfiguration

variable {r : sphere (0 : Plane) 1 → Plane} (cfg : MaeharaConfiguration r)

/-- **Math.** The northern arc is part of the curve. -/
theorem northern_subset : cfg.northern ⊆ Set.range r :=
  cfg.union_eq ▸ subset_union_left

/-- **Math.** The southern arc is part of the curve. -/
theorem southern_subset : cfg.southern ⊆ Set.range r :=
  cfg.union_eq ▸ subset_union_right

/-- **Math.** The midpoint is on the vertical axis. -/
@[simp] theorem midpoint_coord_zero : cfg.midpoint 0 = 0 := by
  rw [cfg.midpoint_eq]; simp

/-- **Math.** Its height is the average of the two points it lies between. -/
theorem midpoint_coord_one :
    cfg.midpoint 1 = (cfg.bottomOfNorthern 1 + cfg.topOfSouthernBelow 1) / 2 := by
  rw [cfg.midpoint_eq]; simp

/-- **Math.** The height of each distinguished point is within the rectangle. -/
theorem bottomOfNorthern_height_mem : cfg.bottomOfNorthern 1 ∈ Icc (-2 : ℝ) 2 :=
  (cfg.subset_rectangle (cfg.northern_subset cfg.bottomOfNorthern_mem)).2

/-- **Math.** … -/
theorem topOfNorthern_height_mem : cfg.topOfNorthern 1 ∈ Icc (-2 : ℝ) 2 :=
  (cfg.subset_rectangle (cfg.northern_subset cfg.topOfNorthern_mem)).2

/-- **Math.** … -/
theorem topOfSouthernBelow_height_mem : cfg.topOfSouthernBelow 1 ∈ Icc (-2 : ℝ) 2 :=
  (cfg.subset_rectangle (cfg.southern_subset cfg.topOfSouthernBelow_mem)).2

/-- **Math.** … -/
theorem bottomOfSouthern_height_mem : cfg.bottomOfSouthern 1 ∈ Icc (-2 : ℝ) 2 :=
  (cfg.subset_rectangle (cfg.southern_subset cfg.bottomOfSouthern_mem)).2

/-- **Math.** The southern arc's distinguished point sits strictly below the
northern arc's: they cannot coincide, because a common point would be an end
of the diameter and those are not on the axis. -/
theorem topOfSouthernBelow_lt_bottomOfNorthern :
    cfg.topOfSouthernBelow 1 < cfg.bottomOfNorthern 1 := by
  rcases lt_or_eq_of_le cfg.topOfSouthernBelow_le with h | h
  · exact h
  · exfalso
    have heq : cfg.topOfSouthernBelow = cfg.bottomOfNorthern := by
      ext i; fin_cases i <;>
        simp [cfg.topOfSouthernBelow_coord_zero, cfg.bottomOfNorthern_coord_zero, h]
    have hmem : cfg.bottomOfNorthern ∈ cfg.northern ∩ cfg.southern :=
      ⟨cfg.bottomOfNorthern_mem, heq ▸ cfg.topOfSouthernBelow_mem⟩
    rw [cfg.inter_eq] at hmem
    exact not_mem_ends_of_coord_zero cfg.bottomOfNorthern_coord_zero hmem

/-- **Math.** The midpoint is strictly above the southern point. -/
theorem topOfSouthernBelow_lt_midpoint :
    cfg.topOfSouthernBelow 1 < cfg.midpoint 1 := by
  rw [cfg.midpoint_coord_one]
  linarith [cfg.topOfSouthernBelow_lt_bottomOfNorthern]

/-- **Math.** And strictly below the northern one. -/
theorem midpoint_lt_bottomOfNorthern :
    cfg.midpoint 1 < cfg.bottomOfNorthern 1 := by
  rw [cfg.midpoint_coord_one]
  linarith [cfg.topOfSouthernBelow_lt_bottomOfNorthern]

/-- **Math.** The midpoint is off the curve. It lies strictly between the
lowest point of the northern arc and the highest point of the southern arc
below it, and on the axis — so it is on neither arc. -/
theorem midpoint_not_mem_range : cfg.midpoint ∈ (Set.range r)ᶜ := by
  intro hmem
  rw [← cfg.union_eq] at hmem
  rcases hmem with hn | hs
  · exact absurd (cfg.bottomOfNorthern_min _ hn cfg.midpoint_coord_zero)
      (not_le.2 cfg.midpoint_lt_bottomOfNorthern)
  · exact absurd (cfg.topOfSouthernBelow_max _ hs cfg.midpoint_coord_zero
      cfg.midpoint_lt_bottomOfNorthern.le) (not_le.2 cfg.topOfSouthernBelow_lt_midpoint)

end MaeharaConfiguration

end JordanCurve
