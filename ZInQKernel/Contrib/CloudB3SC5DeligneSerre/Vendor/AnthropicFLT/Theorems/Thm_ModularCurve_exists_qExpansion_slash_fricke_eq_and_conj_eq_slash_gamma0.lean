/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (git blob 28974d0bf23a116d97177faf9b0cc8611ef72cc8, sha256 f6172644c03b3e19c32c3d71afcd0644453651802f594ab82747da6f036e5351).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n =
        ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
            (((⇑f : UpperHalfPlane → ℂ) ∣[k] W) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n = ι (σ (a n)) := by
  revert M k f hf ι W hW
  exact @_root_.P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.solution
