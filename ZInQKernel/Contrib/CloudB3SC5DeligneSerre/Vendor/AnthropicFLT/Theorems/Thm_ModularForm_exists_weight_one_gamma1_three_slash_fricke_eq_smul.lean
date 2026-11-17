/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul (git blob 0cbec8d5bc16beb57fdb92aa5a6b7f44edbcfc08, sha256 c600a97827ad46e764da01a9ab5a8ce24de962e72302b0f9d8b505d8bce87926).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 1,
      (∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 g).coeff n = (r : ℂ)) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ W : GL (Fin 2) ℝ, (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0] →
        (⇑g : UpperHalfPlane → ℂ) ∣[(1 : ℤ)] W =
          (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑g : UpperHalfPlane → ℂ) := @_root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.solution
