/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Smooth R C]
    {r n : ℕ} (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hby : ∀ i, b (Sum.inl i) = D R C (y i)) (hbz : ∀ j, b (Sum.inr j) = D R C (z j)) :
    ∃ b' : Module.Basis (Fin r ⊕ Fin n)
        (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
        Ω[AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)⁄R],
      (∀ i, b' (Sum.inl i) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (y i))) ∧
      (∀ j, (algebraMap R
          (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)) π) •
          b' (Sum.inr j) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (z j))) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis.solution
