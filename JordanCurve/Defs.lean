/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
module

public import JordanCurve.Arcs
public import JordanCurve.Brouwer
public import JordanCurve.Counting
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.UnitInterval

/-!
# The plane, and the Brouwer interface the argument is stated over

Part of the Jordan curve development; see `PROVENANCE.md` beside this file.
-/

@[expose] public section

namespace JordanCurve

open Metric Set Function Bornology

/-- **Eng.** The plane `ℝ²` as used by the eval problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Eng.** **Brouwer fixed point theorem** (interface). Every continuous self-map of a
nonempty convex compact subset of the plane has a fixed point. Discharged
separately (upstream Mathlib PR #36770, or a standalone build). All of Maehara's
argument is `BrouwerFPT → …`. -/
def BrouwerFPT : Prop :=
  ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x

end JordanCurve
