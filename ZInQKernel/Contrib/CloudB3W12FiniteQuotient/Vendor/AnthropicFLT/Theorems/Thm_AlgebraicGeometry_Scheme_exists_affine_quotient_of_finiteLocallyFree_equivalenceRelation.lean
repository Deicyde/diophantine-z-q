/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean
  Licence        : Apache License, Version 2.0 (see Contrib/CloudB3W12FiniteQuotient/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(port to Lean v4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-16).
The changes are mechanical only; the statement is unchanged:
  * `import P2M.Util` removed; `import P2M.Sol.S_…` retargeted to
    `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_…`.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`
    (so the theorem is
    `ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`).
  * proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` replaced by the direct term
    `P2MW.S_….solution s t hmono hequiv` (the solution in the port namespace).
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.solution
    s t hmono hequiv

end ZInQ.Contrib.CloudW03NeronSurj.FLT
