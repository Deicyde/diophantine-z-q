/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_perm_gamma0_cosetReps (git blob 840cee8223744e4e7d8c40ac558a6223eb1fe9de, sha256 dcec3bd8b9cfef73cc593c7d59180d2519fd635812b6b9724478d513703d6bfb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_perm_gamma0_cosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_perm_gamma0_cosetReps (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ∃ e : Equiv.Perm (Fin (ℓ + 1)), ∀ i : Fin (ℓ + 1), (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ * (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) (e i) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := by
  revert ℓ γ
  exact @_root_.P2MW.S_ModularCurve_exists_perm_gamma0_cosetReps.solution
