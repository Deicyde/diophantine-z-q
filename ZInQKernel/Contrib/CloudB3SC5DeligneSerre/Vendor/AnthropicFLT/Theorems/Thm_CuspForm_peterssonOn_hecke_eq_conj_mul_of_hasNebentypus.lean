/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus (git blob 03d5d39009c4a04e9995bc9cfbbaf15b598c0f5a, sha256 919383013cdd4fef40e551ed4e136358fb76849eaf0dad963c290a59475c9b56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PeterssonOn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f g : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f)
    (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k
        (heckeU k p ⇑f + ε (p : ZMod N) • (⇑f ∣[k] heckeDiagMatrix p)) ⇑g
      = starRingEnd ℂ (ε (p : ZMod N)) *
        CuspForm.peterssonOn (Gamma1 N) k ⇑f
          (heckeU k p ⇑g + ε (p : ZMod N) • (⇑g ∣[k] heckeDiagMatrix p)) := by
  revert N k ε p hp hpN f g hf hg
  exact @_root_.P2MW.S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.solution
