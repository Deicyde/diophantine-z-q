/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd (git blob 05aab3f552f99b3e9280e766450d9c9c9c483b09, sha256 043f3f7e916f521e84c6b43248a45d57ddc4e40afe9672616d92594207f9507e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
    (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (Gamma1 M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, ModularFormClass.qCoeff f (p * n) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ModularFormClass.qCoeff f p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (Gamma1 (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff g (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff g n := by
  revert M k p hp hpM hp2 ε' f hf0 hε hU hT
  exact @_root_.P2MW.S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.solution
