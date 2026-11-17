/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le (git blob 6537e91788b6c281d323a3db337cae0122a518f0, sha256 5d4c5958862fd7e9905ce7aadea7035ef684d1e6b0757f4bafa44bf626b1037a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W) (hPB : P ≤ B) (hP'B' : P' ≤ B')
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (hfin : ∀ M : ℕ, FiniteDimensional k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)))
    (hgen : ∃ M₁ : ℕ, B ≤ ⨆ j : ℕ,
      (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M₁)).map ((φ : W →ₗ[k] W) ^ j))
    (hgen' : ∃ M₁ : ℕ, B' ≤ ⨆ j : ℕ,
      (B' ⊓ B.map ((φ.symm : W →ₗ[k] W) ^ M₁)).map ((φ.symm : W →ₗ[k] W) ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ : W →ₗ[k] W) c y ∈ P)
    (htor' : ∀ y ∈ B', ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ.symm : W →ₗ[k] W) c y ∈ P') :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Module.finrank k ↥(P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)) + Module.finrank k ↥(B ⊓ B') ≤
        Module.finrank k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) +
          Module.finrank k ↥(P ⊓ P') := by
  revert k W φ P B P' B' hPB hP'B' hP hB hP' hB' hfin hgen hgen' htor htor'
  exact @_root_.P2MW.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le.solution
