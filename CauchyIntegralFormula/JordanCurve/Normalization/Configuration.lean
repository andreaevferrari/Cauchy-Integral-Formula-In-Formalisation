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

end MaeharaConfiguration

end JordanCurve
