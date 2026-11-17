/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level (git blob ee3bb687b8335da2675d198615dcb3d163f680f6, sha256 2b9191f827eb0b63e3343ea068fcce0d2cc08eb83936854730b6f2c1794a0e5b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) := by
  revert M k L hLM εL g hg G hG q hq hqM d hd
  exact @_root_.P2MW.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.solution
