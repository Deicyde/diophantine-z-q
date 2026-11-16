/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) [IsSeparated p]
    (p₀ : P₀ ⟶ Spec (CommRingCat.of T)) (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) (μ : P₀ ⟶ A)
    (𝒲 : P.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmμ : ∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ)
    (v : ∀ t : 𝒲.Idx 0, Spec (CommRingCat.of Γ(P, 𝒲.inter t)) ⟶ A)
    (hvf : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      v t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, 𝒲.inter t))))
    (hvm : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter p 𝒲 t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫ v t)
    (hagree : ∀ s : 𝒲.Idx 1, letI := algebraOfHom p (𝒲.inter s)
      letI := algebraOfHom p (𝒲.inter (𝒲.face s 0)); letI := algebraOfHom p (𝒲.inter (𝒲.face s 1))
      Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 1)).toRingHom) ≫ v (𝒲.face s 1) =
        Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 0)).toRingHom) ≫ v (𝒲.face s 0)) :
    ∃ m' : P ⟶ A, m' ≫ f = p ∧ G ≫ m' = μ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree.solution
