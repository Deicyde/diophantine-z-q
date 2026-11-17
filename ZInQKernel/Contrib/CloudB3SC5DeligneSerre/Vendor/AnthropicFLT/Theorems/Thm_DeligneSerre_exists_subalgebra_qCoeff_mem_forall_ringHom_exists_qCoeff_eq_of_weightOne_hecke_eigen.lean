/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen (git blob 9485c19423dd34f92dbff44b29c3ad02806d2278, sha256 ef0cb5210056c81065c70c874f100f22e4dd1924c63846510372ae69b0aa3e82).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      ∃ (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
        (hε : ∀ x : ZMod N, ε x ∈ R),
      ∀ τ : R →+* ℂ, ∃ (ε' : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) 1),
        (∀ x : ZMod N, ε' x = τ ⟨ε x, hε x⟩) ∧
        ModularFormClass.qCoeff g 1 = 1 ∧
        (∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
          ModularFormClass.qCoeff g p = τ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              ε' (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n := by
  revert N ε f hf₁ hT
  exact @_root_.P2MW.S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.solution
