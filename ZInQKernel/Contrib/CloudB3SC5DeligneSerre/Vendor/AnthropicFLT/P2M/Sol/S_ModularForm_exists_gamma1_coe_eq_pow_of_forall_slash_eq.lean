/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq (git blob b9d7ab201306b1cd00170782e8161c6c92e63d61, sha256 1e115d50584af9ceea510569190a556581e6d6eccf476629f25020edd402db71).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (i : ℕ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ P : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * k),
      (∀ t : ZMod M, (⇑(P t) : UpperHalfPlane → ℂ) = (⇑(F t) : UpperHalfPlane → ℂ) ^ i) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(P t) : UpperHalfPlane → ℂ) ∣[(i : ℤ) * k] γ = ⇑(P (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
  induction i with
  | zero =>
    rw [show ((0 : ℕ) : ℤ) * k = 0 by simp]
    refine ⟨fun _ => ModularForm.const 1, fun t => ?_, fun t γ _ => ?_⟩
    · rw [pow_zero]; rfl
    · have h := ModularForm.is_invariant_const γ (1 : ℂ)
      exact h
  | succ i ih =>
    obtain ⟨P, hP1, hP2⟩ := ih
    rw [show ((i + 1 : ℕ) : ℤ) * k = (i : ℤ) * k + k by push_cast; ring]
    refine ⟨fun t => (P t).mul (F t), fun t => ?_, fun t γ hγ => ?_⟩
    · rw [ModularForm.coe_mul, hP1, pow_succ]
    · simp only [ModularForm.coe_mul]
      rw [ModularForm.mul_slash_SL2, hP2 t γ hγ, hF t γ hγ]
