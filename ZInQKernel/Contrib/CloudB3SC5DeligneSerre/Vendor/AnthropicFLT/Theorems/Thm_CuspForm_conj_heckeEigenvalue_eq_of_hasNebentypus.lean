/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus (git blob ef56b6d35f826f162a38d9cd7e396040e829343c, sha256 da0cbe5e88eae2b2e3a0cdaf9950b1a7f3fdd32fa166f8c14e4e2b9dcf2a6b27).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      lam * ModularFormClass.qCoeff g n) :
    starRingEnd ℂ lam = ε⁻¹ (p : ZMod M) * lam := by
  revert M k ε g hg0 hg p hp hpM lam heig
  exact @_root_.P2MW.S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.solution
