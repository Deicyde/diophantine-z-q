/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' A'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hca : a₁ ≫ c = a₂ ≫ c)
    (L' : RelativeGroupLaw S' f') (L'' : RelativeGroupLaw (S' ⊗[S] S') f'')
    (ha₁mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₁ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1)
    (ha₂mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₂ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1) :
    ∃ L : RelativeGroupLaw S f,
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ c =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (L'.IsCommutative → L.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.solution
