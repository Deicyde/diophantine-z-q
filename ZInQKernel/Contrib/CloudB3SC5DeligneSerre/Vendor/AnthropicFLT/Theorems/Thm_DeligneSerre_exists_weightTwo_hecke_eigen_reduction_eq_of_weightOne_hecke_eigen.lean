/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen (git blob b92140b2c7793a7238cf39850dd0efcf16fa0283, sha256 1a151916568c00ecdd603ca0a8535403dbd07d3d43c8ab4034cba66960bc47c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0)) ∧
      ∃ (η : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 2) (b : ℕ → ℂ),
        g ≠ 0 ∧ CuspForm.HasNebentypus η g ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              η (p : ZMod M) * (p : ℂ) *
                (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            b p * ModularFormClass.qCoeff g n) ∧
        ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ) (hη : ∀ x : ZMod M, η x ∈ R')
          (hb : ∀ p : ℕ, p.Prime → ¬ p ∣ M → b p ∈ R'),
          ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M),
            φ' ⟨b p, hb p hp hpM⟩ = φ ⟨ModularFormClass.qCoeff f p, hR p⟩ ∧
            φ' ⟨η (p : ZMod M), hη _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩ := by
  revert N ε f hf₁ hT R hR hε κ φ
  exact @_root_.P2MW.S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.solution
