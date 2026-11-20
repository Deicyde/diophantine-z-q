/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt (git blob e5d4568a5cbf88e459353480e2a106403f92baad, sha256 f6ad02cdc85770e992ed2147a01d148b96a0ffb40e2fc0e68da259fed6a63cf1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_BadPrimes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace NumberField
end NumberField
namespace Ideal
end Ideal
namespace NumberField.Ideal
end NumberField.Ideal
namespace IsArithFrobAt
end IsArithFrobAt
namespace FrobeniusDensity
end FrobeniusDensity
namespace P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.FrobeniusDensity
end P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.FrobeniusDensity

namespace P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt

set_option autoImplicit false

open _root_.NumberField
open _root_.Ideal
open _root_.NumberField.Ideal
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction
attribute [local instance] Ideal.Quotient.field

section OrderBound

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

open Polynomial in
private theorem card_le_of_forall_pow_eq {K : Type*} [CommRing K] [IsDomain K] [Finite K]
    {n : ℕ} (hn : 1 < n) (h : ∀ x : K, x ^ n = x) : Nat.card K ≤ n := by
  cases nonempty_fintype K
  have hdeg : (X ^ n - X : K[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact hn),
      natDegree_X_pow]
  have hne : (X ^ n - X : K[X]) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  rw [mem_roots hne]
  simp [Polynomial.IsRoot, h x]

namespace IsArithFrobAt export _root_.IsArithFrobAt (mem_stabilizer) end IsArithFrobAt
open scoped _root_.IsArithFrobAt in
private theorem IsArithFrobAt.mk_pow_smul' {σ : G} {Q : Ideal S} (h : IsArithFrobAt R σ Q)
    (m : ℕ) (x : S) :
    Ideal.Quotient.mk Q (σ ^ m • x) =
      Ideal.Quotient.mk Q x ^ Nat.card (R ⧸ Q.under R) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Ideal.Quotient.mk Q (σ • (σ ^ m • x)) =
        Ideal.Quotient.mk Q (σ ^ m • x) ^ Nat.card (R ⧸ Q.under R) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact h (σ ^ m • x)
    rw [pow_succ' σ m, mul_smul, h1, ih, ← pow_mul, pow_succ]

open scoped _root_.IsArithFrobAt in
private theorem IsArithFrobAt.card_quotient_le_pow' {σ : G} {Q : Ideal S} [Q.IsPrime]
    [Finite (S ⧸ Q)] (h : IsArithFrobAt R σ Q) {m : ℕ} (hm : m ≠ 0) (hσ : σ ^ m = 1) :
    Nat.card (S ⧸ Q) ≤ Nat.card (R ⧸ Q.under R) ^ m := by
  have hq : 1 < Nat.card (R ⧸ Q.under R) := by
    have h1 : Finite (R ⧸ Q.under R) := h.finite_quotient
    have h2 : (Q.under R).IsPrime := Ideal.IsPrime.comap _
    have h3 : Nontrivial (R ⧸ Q.under R) := Ideal.Quotient.nontrivial_iff.mpr h2.ne_top
    exact Finite.one_lt_card
  refine card_le_of_forall_pow_eq (Nat.one_lt_pow hm hq) fun y ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← IsArithFrobAt.mk_pow_smul' h m x, hσ, one_smul]

end OrderBound

namespace FrobeniusDensity
export _root_.FrobeniusDensity (card_quotient_ratPrimeIdeal card_quotient_under_int ratPrimeIdeal ratPrimeIdeal_ne_bot finite_quotient_of_ne_bot ne_bot_of_liesOver_ratPrimeIdeal)
open _root_.FrobeniusDensity

private theorem isSeparable_residue' {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Algebra.IsSeparable (ℤ ⧸ ratPrimeIdeal ℓ) ((𝓞 L) ⧸ Q) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  haveI : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot hQbot
  haveI : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
    Ring.HasFiniteQuotients.finiteQuotient (ratPrimeIdeal_ne_bot hℓ)
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hQbot
  haveI : (ratPrimeIdeal ℓ).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ))).isMaximal (ratPrimeIdeal_ne_bot hℓ)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end FrobeniusDensity

open _root_.FrobeniusDensity
open _root_.P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.FrobeniusDensity

theorem solution
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    MulAction.stabilizer (L ≃ₐ[ℚ] L) Q
      = Subgroup.zpowers (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  haveI : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot hQbot
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hQbot
  haveI : (ratPrimeIdeal ℓ).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ))).isMaximal (ratPrimeIdeal_ne_bot hℓ)
  haveI : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
    Ring.HasFiniteQuotients.finiteQuotient (ratPrimeIdeal_ne_bot hℓ)
  haveI := isSeparable_residue' (L := L) hℓ Q
  have hfrob : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) Q :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q
  have hle : Subgroup.zpowers (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
      ≤ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q :=
    Subgroup.zpowers_le.mpr hfrob.mem_stabilizer
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L) Q)
      = Module.finrank (ℤ ⧸ ratPrimeIdeal ℓ) ((𝓞 L) ⧸ Q) := by
    rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (ratPrimeIdeal ℓ) Q, hinertia]
    simp [Ideal.inertiaDeg_eq_of_isMaximal (ratPrimeIdeal ℓ) Q]
  have hord : Module.finrank (ℤ ⧸ ratPrimeIdeal ℓ) ((𝓞 L) ⧸ Q)
      ≤ orderOf (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    have hbound := IsArithFrobAt.card_quotient_le_pow' hfrob
      (orderOf_pos (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).ne' (pow_orderOf_eq_one _)
    rw [card_quotient_under_int (ℓ := ℓ) Q, Module.natCard_eq_pow_finrank
      (K := ℤ ⧸ ratPrimeIdeal ℓ) (V := (𝓞 L) ⧸ Q), card_quotient_ratPrimeIdeal] at hbound
    exact (Nat.pow_le_pow_iff_right hℓ.one_lt).mp hbound
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact hord
