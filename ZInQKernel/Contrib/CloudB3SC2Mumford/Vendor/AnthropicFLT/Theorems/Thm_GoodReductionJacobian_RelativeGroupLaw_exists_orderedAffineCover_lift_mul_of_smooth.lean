/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_lift_mul_of_smooth
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    ∃ (𝒲 : (pullback f f).OrderedAffineCover) (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A),
      (∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f) ∧
      (∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth.solution
