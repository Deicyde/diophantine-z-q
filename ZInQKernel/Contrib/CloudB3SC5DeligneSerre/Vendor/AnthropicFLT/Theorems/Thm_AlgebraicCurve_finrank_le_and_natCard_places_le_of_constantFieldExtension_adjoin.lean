/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin (git blob a6e87a6965e14a14ec97bbcf24ceb4ea94b3a1c5, sha256 f3002e10da7c9a46453d05e1fe2d913340fbffd04b894813c90240d87e1fce64).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped IntermediateField

theorem AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {F : Type*} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (y : F) (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set F)) F]
    {K' : Type*} [Field K'] [Algebra k K']
    {L : Type*} [Field L] [Algebra K' L] (t : L) (ht : Transcendental K' t)
    (E : IntermediateField (IntermediateField.adjoin K' ({t} : Set L)) L)
    [FiniteDimensional (IntermediateField.adjoin K' ({t} : Set L)) E]
    [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]
    (hyt : (algebraMap F E y : L) = t)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤) :
    Module.finrank (IntermediateField.adjoin k ({y} : Set F)) F ≤
        Module.finrank (IntermediateField.adjoin K' ({t} : Set L)) E ∧
      ∀ u : F, u ≠ 0 →
        (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
            Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
        (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
            Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by
  revert k F y hy K' L t ht E hyt hgen
  exact @_root_.P2MW.S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.solution
