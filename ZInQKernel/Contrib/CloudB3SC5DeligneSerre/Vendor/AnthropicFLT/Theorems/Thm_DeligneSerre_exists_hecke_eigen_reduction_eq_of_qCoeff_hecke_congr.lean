/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr (git blob 83e6e35964ef5e9a3daf81798e3a7b64a0822da5, sha256 d8f9a78249aa98e1ce87e70a797565509130ef1aa1a90f55cf594e38c8c58596).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
    (N : ℕ) [NeZero N] (w : ℕ) (ε : DirichletCharacter ℂ N)
    (h : CuspForm (Gamma1 N) w) (hεh : CuspForm.HasNebentypus ε h)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff h n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ)
    (hne : ∃ n : ℕ, φ ⟨ModularFormClass.qCoeff h n, hR n⟩ ≠ 0)
    (α : ℕ → R)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 → ∀ n : ℕ, ∃ r : R,
        (r : ℂ) = ModularFormClass.qCoeff h (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) ∧
        φ r = φ (α p) * φ ⟨ModularFormClass.qCoeff h n, hR n⟩) :
    ∃ (g : CuspForm (Gamma1 N) w) (b : ℕ → ℂ), g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ),
        (∀ x : ZMod N, ∃ hx : ε x ∈ R', φ' ⟨ε x, hx⟩ = φ ⟨ε x, hε x⟩) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 →
          ∃ hb : b p ∈ R', φ' ⟨b p, hb⟩ = φ (α p) := by
  revert N w ε h hεh R hR hε κ φ hne α hT
  exact @_root_.P2MW.S_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.solution
