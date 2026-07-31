/-
Copyright (c) 2026 Andrea E. V. Ferrari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea E. V. Ferrari
-/
module

-- The lakefile sets Mathlib's own linter options (`linter.flexible`,
-- `linter.mathlibStandardSet`), which only exist once Mathlib is imported: a
-- file of this project that imports nothing at all fails to elaborate.
public import Mathlib.Analysis.Complex.Basic

/-!
# Basic

The first file of the project. It exists so that the library and the continuous
integration have something to build; it carries no mathematics yet.

Add real files alongside it under `CauchyIntegralFormula/`, then run
`lake exe mk_all --module` to regenerate the root import file
`CauchyIntegralFormula.lean` — CI checks that it is up to date.
-/
