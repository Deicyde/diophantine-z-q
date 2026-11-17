/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span.solution
