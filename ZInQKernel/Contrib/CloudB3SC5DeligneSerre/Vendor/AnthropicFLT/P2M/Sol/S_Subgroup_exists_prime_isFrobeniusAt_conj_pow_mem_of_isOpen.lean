/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen (git blob 59315ced5ac728e4656a3ebf50b6b4cf91c1633b, sha256 ea73ce08fb22f9db33b9e17e06bdc2d3edb88a17afcc535fe7bbe9a3033717b2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen

theorem solution
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by

  obtain ⟨F, hF, hNF, hGal, hAlg, hST, hker⟩ :=
    hH.exists_numberField_ker_restrictNormalHom_le
  letI := hF; letI := hNF; letI := hGal; letI := hAlg; letI := hST

  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.frobeniusPowerDense_of_le_ker F hker M.primeFactors σ

  exact ⟨ℓ, A, τ, g, n, hℓ,
    fun hdvd => hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hM.ne'⟩),
    hA, hτ, hmem⟩
