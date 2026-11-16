/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean
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
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.solution s t hmono hequiv haff

end ZInQ.Contrib.CloudW03NeronSurj.FLT
