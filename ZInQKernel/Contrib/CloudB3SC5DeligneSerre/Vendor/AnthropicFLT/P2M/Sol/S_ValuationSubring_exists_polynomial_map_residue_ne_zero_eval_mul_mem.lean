/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem (git blob 54e761c5d6707bcb85549f41213a891c6bde2fbd, sha256 bc616f6b97def9ebc00d8281c24d6af5edccd1fbe9047f333670d616ffed89da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q : Polynomial A, (q.map (IsLocalRing.residue A)) ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V →
        (Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q) * z ∈ V := by
  classical

  obtain ⟨q₀, hq₀0, hq₀T⟩ := Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (L := L) f z

  have hmem : (↑q₀ : F) ∈ (Polynomial.aeval (R := L) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact q₀.2
  obtain ⟨q₁, hq₁⟩ := hmem
  have hq₁0 : q₁ ≠ 0 := by
    rintro rfl; simp only [map_zero] at hq₁
    exact hq₀0 (Subtype.ext hq₁.symm)

  obtain ⟨q, c, hc0, hqmap, hqbar⟩ := ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero A q₁ hq₁0
  refine ⟨q, hqbar, fun V hL hfV => ?_⟩

  have heval : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
      algebraMap L F c⁻¹ * (q₀ : F) := by
    have h1 : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
        Polynomial.aeval f (q.map A.subtype) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [h1, hqmap, map_mul, aeval_C]
    exact congrArg _ hq₁
  rw [heval, mul_assoc]
  exact mul_mem (hL c⁻¹) (hq₀T V hL hfV)
