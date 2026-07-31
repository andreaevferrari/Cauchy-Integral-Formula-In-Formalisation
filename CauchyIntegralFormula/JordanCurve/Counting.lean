/-
Copyright (c) 2026 rkirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rkirov, Xinze Li
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Subtype

@[expose] public section

/-!
# Counting connected components

Pure topology, with no geometry in it: the lemmas that turn "the complement of
the curve has two pieces" into the numerical statement
`Nat.card (ConnectedComponents X) = 2`.

The separation argument works with `connectedComponentIn S x` for a set `S` and
distinguished points inside it. The counting statement is about the quotient
type `ConnectedComponents S`. Those are two different objects, and the bridge
between them is what this file is for:

* `nat_card_connectedComponents_eq_two` — two points in distinct components that
  between them exhaust the space give exactly two components;
* `connectedComponents_subtype_eq_iff` and its `mem`-flavoured restatement —
  equality of classes in the quotient is equality of `connectedComponentIn`
  subsets, so the geometry side never has to mention the quotient.

## Provenance

Adapted from `rkirov/jordan_pick`, Apache 2.0 — see
`CauchyIntegralFormula/External/JordanCurve/MODIFICATIONS.md` for the full
provenance of the development this was taken from. The statements and proofs
are the original author's; what changed here is the imports (`import Mathlib`
narrowed to the six modules actually used), the docstring tags, and this
header.
-/

namespace JordanCurve.Counting

open Set

variable {X : Type*} [TopologicalSpace X]

/-- **Math.** If a space has two points lying in distinct connected components,
and every point's component is one of those two, then the space has exactly two
connected components. -/
theorem nat_card_connectedComponents_eq_two
    (a b : X) (hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b)
    (hcover : ∀ x : X, ConnectedComponents.mk x = ConnectedComponents.mk a
                     ∨ ConnectedComponents.mk x = ConnectedComponents.mk b) :
    Nat.card (ConnectedComponents X) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk a, ConnectedComponents.mk b, hab, ?_⟩
  rw [eq_univ_iff_forall]
  intro z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  rcases hcover x with h | h
  · exact mem_insert_iff.mpr (Or.inl h)
  · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr h))

/-- **Eng.** The bridge between the two ways of naming a component: for two
points of a subset `S`, the connected components of the corresponding subtype
points agree exactly when their `connectedComponentIn S` subsets agree.

This is plumbing, not mathematics — it exists so that the separation argument
can phrase everything with `connectedComponentIn` and never mention the
quotient type that the counting statement is about. -/
theorem connectedComponents_subtype_eq_iff {S : Set X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) :
    ConnectedComponents.mk (⟨x, hx⟩ : S) = ConnectedComponents.mk (⟨y, hy⟩ : S)
      ↔ connectedComponentIn S x = connectedComponentIn S y := by
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy,
    (image_injective.mpr Subtype.coe_injective).eq_iff,
    ← ConnectedComponents.coe_eq_coe]

/-- **Eng.** The `mem`-flavoured restatement of the bridge: the classes agree
exactly when `y` lies in the component of `x`. This is the form the separation
argument actually applies. -/
theorem connectedComponents_subtype_eq_iff_mem {S : Set X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) :
    ConnectedComponents.mk (⟨x, hx⟩ : S) = ConnectedComponents.mk (⟨y, hy⟩ : S)
      ↔ y ∈ connectedComponentIn S x := by
  rw [connectedComponents_subtype_eq_iff hx hy]
  exact ⟨fun h => h.symm ▸ mem_connectedComponentIn hy,
    fun h => connectedComponentIn_eq h⟩

end JordanCurve.Counting
