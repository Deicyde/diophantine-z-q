/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField.solution
