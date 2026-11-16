/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (A : Type u) [CommRing A] [Algebra R A] {i : ℕ} (s : 𝒰.Idx i) :
    letI := algebraOfHom π (𝒰.inter s)
    letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter s)
    ∃ σ : (A ⊗[R] Γ(X, 𝒰.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s),
      (∀ x : Γ(X, 𝒰.inter s),
        σ ((1 : A) ⊗ₜ[R] x) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter s)).hom x)) ∧
      (∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, 𝒰.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter.solution
