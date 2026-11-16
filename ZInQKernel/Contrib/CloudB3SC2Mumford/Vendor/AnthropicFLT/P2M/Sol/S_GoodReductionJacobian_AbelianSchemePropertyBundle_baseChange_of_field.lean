/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) {k : Type u} [Field k]
    (ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    AbelianSchemePropertyBundle k (pullback.snd f ι) := by
  refine ⟨MorphismProperty.pullback_snd (P := @Smooth) f ι hA.smooth,
    MorphismProperty.pullback_snd (P := @IsProper) f ι hA.proper, fun s => ?_,
    hA.hasGroupLaw.map fun G => G.baseChange ι⟩
  have hGI : GeometricallyIntegral f :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber f).2 fun s =>
      (abelianSchemePropertyBundle_fibreStr hA s).geometricallyIntegral
  have hInt : IsIntegral (pullback f ι) :=
    pullback_of_geometrically hGI.geometrically_isIntegral k ι
  have huniv : (pullback.snd f ι).base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [huniv]
  exact (IrreducibleSpace.isIrreducible_univ _).isConnected
