/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 (git blob 6d0c8a05e8a606f88610102f65af9498760511b2, sha256 c9e357457f7cc73eb68c50368c70b1fca399de3f124065a3fcebd0ba3900256e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ε ((γ 1 1 : ℤ) : ZMod N) • f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (heckeU k p f + ε (p : ZMod N) • (f ∣[k] heckeDiagMatrix p)) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      = ε ((γ 1 1 : ℤ) : ZMod N) • (heckeU k p f + ε (p : ZMod N) • (f ∣[k] heckeDiagMatrix p)) := by
  revert N k p hp hpN ε f hf γ hγ
  exact @_root_.P2MW.S_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0.solution
