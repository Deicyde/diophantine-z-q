import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AdicThickening
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete

/-!
# Uniqueness of morphisms out of a proper scheme over a complete adic ring

Two morphisms from a proper scheme to a separated scheme over a complete noetherian adic ring that
agree on every adic thickening are equal. This is the vendored Fermat theorem
`AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete`,
restated with the `adicThickening` vocabulary used by the group-law pipeline.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ZInQ.Contrib.CloudB3SC2Mumford

theorem eq_of_forall_adicThickening_comp_eq_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsSeparated g] {ψ ψ' : X ⟶ Y} (hψ : ψ ≫ g = f) (hψ' : ψ' ≫ g = f)
    (h : ∀ n : ℕ, adicThickeningι f I n ≫ ψ = adicThickeningι f I n ≫ ψ') : ψ = ψ' :=
  AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
    R I f g (fun n => adicThickeningBase I n) (fun n => by rw [Ideal.Quotient.algebraMap_eq]) ψ ψ' hψ hψ'
    (fun n => h n)

end ZInQ.Contrib.CloudB3SC2Mumford
