/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open KaehlerDifferential MvPolynomial

universe u

theorem MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential.solution
