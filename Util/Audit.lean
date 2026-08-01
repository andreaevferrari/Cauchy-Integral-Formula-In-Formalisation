/-
Copyright (c) 2026 Andrea E. V. Ferrari, Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari, Xinze Li
-/
import Lean

/-!
# `lake exe jordan-audit`

One-command health check for this library. Performs:

1. **Public-API listing.** Prints the declarations the hypergraph's cards
   name in their `lean:` frontmatter, and confirms each is present in the
   imported environment. A missing declaration is a hard failure — a card
   pointing at a name that no longer exists is worse than a card pointing
   at nothing.
2. **Foundational-axiom audit.** Walks the proof terms of those theorems via
   `Environment.find?` + `Expr.foldConsts`, transitively collecting every
   `axiomInfo` reachable from the proof. Confirms that the only foundational
   axioms reached are `propext`, `Classical.choice` and `Quot.sound`. Any
   other axiom — `sorryAx` above all — causes a non-zero exit.

The exit code is `0` on success and `1` on any failure. Intended for both
interactive use and CI.

**Why this exists before anything is refactored.** The Jordan curve
development this library carries is being reorganised from the four files it
arrived in. Every such step can quietly break a proof or weaken a statement,
and without an audit there is no way to tell a successful refactor from one
that introduced a gap: `lake build` succeeding proves only that the files
elaborate, not that the theorems still rest on nothing.

The audit catches an unexpected axiom. It does NOT catch a statement that
has been weakened — for that, see `JordanCurve.Anchor`,
which restates the theorem verbatim and will stop compiling if an internal
statement drifts.

This file deliberately avoids importing the library statically: that would
force the audit executable to link the entire transitive Mathlib closure,
which exceeds macOS's `ARG_MAX` linker argument limit. Target names are
built as `Name` literals and the library is loaded at runtime via
`importModules`.
-/

open Lean

/-- Build `JordanCurve.<s>` without needing the constant in scope (which
would force a static import of the audited module). -/
private def jc (s : String) : Name :=
  .str (.str .anonymous "JordanCurve") s

/-- Build `JordanCurve.Brouwer.<s>`. -/
private def jcb (s : String) : Name :=
  .str (.str (.str .anonymous "JordanCurve") "Brouwer") s

/-- Foundational axioms expected for every public theorem. -/
private def expectedAxioms : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

/-- The axioms a constant transitively depends on.

This calls Lean's own `collectAxioms` — the one behind `#print axioms` —
rather than walking `ConstantInfo.value?` by hand. A hand-rolled walk was
tried first and was **silently vacuous**: under the module system an
imported environment is in its *exporting* view, where a theorem's proof
term is not reachable, so `value?` yields nothing, the walk terminates
immediately, and every theorem is pronounced clean. It passed a
deliberately planted `sorry`.

`collectAxioms` opens `env.setExporting false` before walking, which is the
step that was missing, and it also reads the pre-computed axiom sets that
imported declarations carry. Do not replace it with something local. -/
private def axiomsOf (env : Environment) (thm : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<jordan-audit>", fileMap := default }
  let (axs, _) ← Core.CoreM.toIO (Lean.collectAxioms thm) ctx { env := env }
  return axs

/-- Audit one named theorem. Returns `true` on success. -/
private def auditTheorem (env : Environment) (thm : Name) : IO Bool := do
  let axs ← axiomsOf env thm
  let unexpected := axs.toList.filter (fun a => !expectedAxioms.contains a)
  if unexpected.isEmpty then
    IO.println s!"  ✓ {thm}"
    return true
  else
    IO.println s!"  ✗ {thm} — unexpected axioms: {unexpected}"
    return false

/-- Public definitions: the vocabulary the theorems below are stated in. -/
private def publicDefs : List (Name × String) :=
  [ (jc "Plane",      "abbrev     (the plane ℝ², as EuclideanSpace ℝ (Fin 2))")
  , (jc "BrouwerFPT", "def        (Brouwer fixed point theorem, as an interface)") ]

/-- Theorems audited for axiom purity: every declaration named by a card's
`lean:` frontmatter, plus the interface discharge that makes them
unconditional. -/
private def publicTheorems : List (Name × String) :=
  [ (jc "jordan_curve",
       "theorem    (thm-jordan-curve: the complement has exactly two components)")
  , (jc "exists_unbounded_component",
       "theorem    (thm-jordan-curve: an unbounded component exists)")
  , (jc "unbounded_component_unique",
       "theorem    (thm-jordan-curve: it is the only one)")
  , (jc "exists_bounded_component",
       "theorem    (thm-jordan-curve: a bounded component exists — what `inside` means)")
  , (jc "component_boundary_eq",
       "theorem    (thm-jordan-curve: the curve is the boundary of each component)")
  , (jcb "brouwerFPT",
       "theorem    (discharges the BrouwerFPT interface: the results above are unconditional)") ]

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    #[(`JordanCurve : Import)] {} (trustLevel := 0)

  IO.println "JordanCurve library audit"
  IO.println "=========================="
  IO.println ""

  let mut allOk := true

  IO.println "Public definitions:"
  for (n, kind) in publicDefs do
    if env.contains n then
      IO.println s!"  • {n}\n      {kind}"
    else
      IO.println s!"  ✗ {n} — NOT FOUND in environment"
      allOk := false
  IO.println ""

  IO.println "Public theorems:"
  for (n, kind) in publicTheorems do
    if env.contains n then
      IO.println s!"  • {n}\n      {kind}"
    else
      IO.println s!"  ✗ {n} — NOT FOUND in environment"
      allOk := false
  IO.println ""

  IO.println "Foundational-axiom audit:"
  for (thm, _) in publicTheorems do
    if env.contains thm then
      let ok ← auditTheorem env thm
      if !ok then allOk := false
  IO.println ""

  if allOk then
    IO.println "Every audited theorem depends only on:"
    IO.println "  propext, Classical.choice, Quot.sound"
    IO.println ""
    IO.println "Library status: ✓ healthy"
    return 0
  else
    IO.println "Library status: ✗ audit FAILED"
    return 1
