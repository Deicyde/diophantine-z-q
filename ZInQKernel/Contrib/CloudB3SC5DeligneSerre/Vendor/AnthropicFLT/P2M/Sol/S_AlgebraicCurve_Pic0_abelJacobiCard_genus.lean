/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_abelJacobiCard_genus (git blob b491f20c7665ef490ed4f6b6357e8f6056197c98, sha256 1a396de4ade719e1fdeb10a2cd86c51a0b3543df73ad73150e1f3735f5ad5c25).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve
namespace AlgebraicCurve.Pic0
end AlgebraicCurve.Pic0
namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0
end P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0
namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0.AbelJacobiCardReduction
end P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0.AbelJacobiCardReduction

namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Pic Pic0 Pic0.torsion AbelJacobiCard IsCurveOver HasCanonicalDivisor genus Pic0.natCard_torsion_prime_eq_pow_genus Pic0.exists_nsmul_eq)
namespace Pic0
export _root_.AlgebraicCurve.Pic0 (torsion natCard_torsion_prime_eq_pow_genus exists_nsmul_eq)
namespace AbelJacobiCardReduction
open _root_.AlgebraicCurve.Pic0
open _root_.AlgebraicCurve

variable {A : Type*} [AddCommGroup A]

abbrev tors (A : Type*) [AddCommGroup A] (m : ℕ) : AddSubgroup A :=
  (Submodule.torsionBy ℤ A (m : ℤ)).toAddSubgroup

theorem mem_tors {m : ℕ} {x : A} : x ∈ tors A m ↔ (m : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

theorem mem_tors_iff_nsmul {m : ℕ} {x : A} : x ∈ tors A m ↔ m • x = 0 := by
  rw [mem_tors, natCast_zsmul]

theorem natCard_tors_one : Nat.card (tors A 1) = 1 := by
  have h : tors A 1 = ⊥ := by
    refine (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    simpa [mem_tors_iff_nsmul] using hx
  rw [h]
  exact Nat.card_unique

theorem nsmul_mem_tors_pow {p n : ℕ} {x : A} (hx : x ∈ tors A (p ^ (n + 1))) :
    p • x ∈ tors A (p ^ n) := by
  rw [mem_tors_iff_nsmul] at hx ⊢
  rw [← mul_nsmul', ← pow_succ, hx]

def mulP (A : Type*) [AddCommGroup A] (p n : ℕ) : tors A (p ^ (n + 1)) →+ tors A (p ^ n) where
  toFun x := ⟨p • (x : A), nsmul_mem_tors_pow x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp]
theorem coe_mulP_apply (p n : ℕ) (x : tors A (p ^ (n + 1))) :
    ((mulP A p n x : tors A (p ^ n)) : A) = p • (x : A) := rfl

theorem mulP_surjective {p n : ℕ} (hdiv : ∀ x : A, ∃ y : A, p • y = x) :
    Function.Surjective (mulP A p n) := by
  intro x
  obtain ⟨y, hy⟩ := hdiv (x : A)
  have hy' : y ∈ tors A (p ^ (n + 1)) := by
    rw [mem_tors_iff_nsmul, pow_succ, mul_nsmul', hy]
    exact (mem_tors_iff_nsmul).mp x.2
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def kerMulPEquiv (p n : ℕ) : (mulP A p n).ker ≃ tors A p where
  toFun x := ⟨((x : tors A (p ^ (n + 1))) : A), by
    have hx := x.2
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff, coe_mulP_apply] at hx
    exact (mem_tors_iff_nsmul).mpr hx⟩
  invFun y := ⟨⟨(y : A), by
      have hy := (mem_tors_iff_nsmul).mp y.2
      rw [mem_tors_iff_nsmul, pow_succ, mul_nsmul', hy, nsmul_zero]⟩, by
    rw [AddMonoidHom.mem_ker, Subtype.ext_iff, coe_mulP_apply]
    exact (mem_tors_iff_nsmul).mp y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

theorem natCard_tors_pow_succ {p : ℕ} (n : ℕ) (hdiv : ∀ x : A, ∃ y : A, p • y = x) :
    Nat.card (tors A (p ^ (n + 1))) = Nat.card (tors A p) * Nat.card (tors A (p ^ n)) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP A p n).ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (mulP A p n)
      (mulP_surjective hdiv)).toEquiv,
    Nat.card_congr (kerMulPEquiv (A := A) p n), mul_comm]

theorem natCard_tors_pow_eq {p g : ℕ} (hcard : Nat.card (tors A p) = p ^ (2 * g))
    (hdiv : ∀ x : A, ∃ y : A, p • y = x) (n : ℕ) :
    Nat.card (tors A (p ^ n)) = p ^ (2 * g * n) := by
  induction n with
  | zero => rw [pow_zero, mul_zero, pow_zero]; exact natCard_tors_one
  | succ n ih =>
      rw [natCard_tors_pow_succ n hdiv, hcard, ih, ← pow_add]
      congr 1
      ring

end AlgebraicCurve.Pic0.AbelJacobiCardReduction
open scoped _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0 _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0.AbelJacobiCardReduction
open scoped _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve.Pic0
open scoped _root_.P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genus.AlgebraicCurve

open AlgebraicCurve.Pic0.AbelJacobiCardReduction in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (p : ℕ) [Fact p.Prime] :
    AbelJacobiCard K F p (genus K F) := by
  intro n
  have hcard : Nat.card (tors (Pic0 K F) p) = p ^ (2 * genus K F) :=
    AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus K F hfg p
  have hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, p • y = x :=
    AlgebraicCurve.Pic0.exists_nsmul_eq K F hfg p (Fact.out : p.Prime).ne_zero
  exact natCard_tors_pow_eq hcard hdiv n
