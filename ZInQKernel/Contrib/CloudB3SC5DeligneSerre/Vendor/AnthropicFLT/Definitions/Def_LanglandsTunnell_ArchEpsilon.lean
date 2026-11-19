/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_LanglandsTunnell_ArchEpsilon (git blob 1b0946891a4dca521f78381278f3d2fb3c37eadd, sha256 7de688d466d289822a64d19c6615db80d2b66bd46a7413a56c695bf445d39827).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I

@[simp] theorem signEpsilon_zero : signEpsilon 0 = 1 := by simp [signEpsilon]

@[simp] theorem signEpsilon_one : signEpsilon 1 = I := by simp [signEpsilon]

theorem signEpsilon_sq (a : ZMod 2) : signEpsilon a ^ 2 = if a = 0 then 1 else -1 := by
  by_cases h : a = 0
  · simp [signEpsilon, h]
  · simp [signEpsilon, h, I_sq]

namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

@[simp] theorem epsilonFactor_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor = signEpsilon a₁ * signEpsilon a₂ := rfl

@[simp] theorem epsilonFactor_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor = I ^ (k + 1) := rfl

theorem epsilonFactor_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).epsilonFactor = P.epsilonFactor := by
  cases P <;> simp [twist, epsilonFactor]

theorem epsilonFactor_dual (P : RealArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  cases P <;> rfl

theorem epsilonFactor_principal_sq (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor ^ 2 = signEpsilon a₁ ^ 2 * signEpsilon a₂ ^ 2 :=
  mul_pow _ _ _

theorem epsilonFactor_discrete_sq (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor ^ 2 = (-1) ^ (k + 1) := by
  rw [epsilonFactor_discrete, ← pow_mul, mul_comm, pow_mul, I_sq]

theorem epsilonFactor_oddArtin : RealArchParam.oddArtin.epsilonFactor = I := by
  simp [RealArchParam.oddArtin, epsilonFactor]

end RealArchParam

namespace ComplexArchParam

def epsilonFactor (P : ComplexArchParam) : ℂ :=
  I ^ P.k₁.natAbs * I ^ P.k₂.natAbs

theorem epsilonFactor_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).epsilonFactor = P.epsilonFactor := by
  simp [twist, epsilonFactor]

theorem epsilonFactor_dual (P : ComplexArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  simp [dual, epsilonFactor, Int.natAbs_neg]

theorem epsilonFactor_mul_epsilonFactor_dual (P : ComplexArchParam) :
    P.epsilonFactor * P.dual.epsilonFactor = (-1) ^ (P.k₁.natAbs + P.k₂.natAbs) := by
  rw [epsilonFactor_dual, epsilonFactor, ← pow_add, ← pow_add,
    show P.k₁.natAbs + P.k₂.natAbs + (P.k₁.natAbs + P.k₂.natAbs) = 2 * (P.k₁.natAbs + P.k₂.natAbs) by ring,
    pow_mul, I_sq]

theorem epsilonFactor_trivialArtin : ComplexArchParam.trivialArtin.epsilonFactor = 1 := by
  simp [ComplexArchParam.trivialArtin, epsilonFactor]

end ComplexArchParam

end LanglandsTunnell

end
