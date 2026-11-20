/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_isFrickeAutFull (git blob 815c4356214213a432e56a62dbce51144568e1b9, sha256 919b18225b438061d995e824c49cd15f1ea44a099aae39468fd997774961b97d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isFrickeAut
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_full_eq_of_prime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_exists_isFrickeAutFull.ModularCurve
end P2MW.S_ModularCurve_exists_isFrickeAutFull.ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace IntermediateField
end IntermediateField

namespace P2MW.S_ModularCurve_exists_isFrickeAutFull

set_option autoImplicit false

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_exists_isFrickeAutFull.ModularCurve
open _root_.AlgebraicCurve
open _root_.IntermediateField

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (IsFrickeAutFull qExpand qExpand_one_apply jq jqN modularFunctionField modularFunctionFieldFull exists_isFrickeAut full_eq_of_prime)
open _root_.ModularCurve

namespace W2B

theorem cast_algEquiv_exists {E E' : IntermediateField ℚ (LaurentSeries ℚ)} (h : E = E') (σ : E ≃ₐ[ℚ] E) :
    ∃ σ' : E' ≃ₐ[ℚ] E', ∀ x : E', ((σ' x : E') : LaurentSeries ℚ) = σ ⟨x, h ▸ x.2⟩ := by
  subst h
  exact ⟨σ, fun _ => rfl⟩

end W2B

end ModularCurve

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hfull : modularFunctionFieldFull ℓ = modularFunctionField ℓ := ModularCurve.full_eq_of_prime hℓ.out
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isFrickeAut ℓ
  obtain ⟨σ', hσ'⟩ := ModularCurve.W2B.cast_algEquiv_exists hfull.symm σ
  refine ⟨σ', ?_⟩
  intro a b hab _ _
  have hcases : a = 1 ∧ ℓ = b ∨ ℓ = a ∧ b = 1 := by
    have hprime : (a * b).Prime := hab ▸ hℓ.out
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · right; exact ⟨hab.symm.trans (mul_one a), rfl⟩
    · left; exact ⟨rfl, hab.symm.trans (one_mul b)⟩

  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jq →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ jq := by
      rintro y hy rfl
      exact congrArg Subtype.val hσ.1
    apply Subtype.ext
    rw [hσ']
    exact H _ _ (qExpand_one_apply jq)
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jqN ℓ →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ 1 jq := by
      rintro y hy rfl
      exact (congrArg Subtype.val hσ.2).trans (qExpand_one_apply jq).symm
    apply Subtype.ext
    rw [hσ']
    exact H _ _ rfl

end
