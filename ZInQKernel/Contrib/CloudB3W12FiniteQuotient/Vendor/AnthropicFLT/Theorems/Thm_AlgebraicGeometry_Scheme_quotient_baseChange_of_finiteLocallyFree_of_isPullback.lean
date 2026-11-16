/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean
  Licence        : Apache License, Version 2.0 (copyright and licence terms of the source
                   project; see its LICENSE, NOTICE and ATTRIBUTION.md)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof step was
altered, weakened or omitted except as listed below:
  * `import P2M.Util` removed (no custom commands/tactics are used).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.*`.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * `set_option maxHeartbeats 4000000` and `set_option synthInstance.maxHeartbeats 400000` added
    (the source lakefile sets these globally).
  * 1 top-level `open` command(s): each namespace written as `_root_.<ns>` so that it
    resolves to the Mathlib namespace and not to a same-named namespace under the port prefix
    (e.g. `ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry`).
  * the proof `by p2m_exact_reverting @_root_.P2MW.….solution` replaced by the direct term
    `P2MW.….solution <the explicit hypotheses>` (same solution, now under the port namespace).
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) :=
  P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.solution hR hX hsq htq w'

end ZInQ.Contrib.CloudW03NeronSurj.FLT
