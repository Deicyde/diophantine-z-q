import ZInQKernel.Contrib.CMSerreTateSupport.WildTraceV004
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite wild displacement groups are residue-characteristic groups

The subgroup is defined by the literal strict valuation displacement
condition on field automorphisms. Its closure laws are proved. Scalar
trace excludes every unit-prime order, and Cauchy's theorem then shows
that its finite cardinality has no other prime factor.
-/

noncomputable section
set_option autoImplicit false

namespace WildFiniteGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The actual strict displacement subgroup, with no abstract wild-action model. -/
def strictDisplacementGroup (w : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : L, x ≠ 0 → w.valuation (σ x - x) < w.valuation x}
  one_mem' := by
    intro x hx
    simpa using (w.valuation.pos_iff.mpr hx)
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
    have hsmall := hσ (τ x) hτx
    rw [WildTrace.valuation_apply_eq w.valuation τ hτ x] at hsmall
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [he]
    exact w.valuation.map_add_lt hsmall (hτ x hx)
  inv_mem' := by
    intro σ hσ x hx
    have hy : σ⁻¹ x ≠ 0 := (map_ne_zero σ⁻¹).mpr hx
    have hcancel : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have hval : w.valuation (σ⁻¹ x) = w.valuation x := by
      have h := WildTrace.valuation_apply_eq w.valuation σ hσ (σ⁻¹ x)
      rw [hcancel] at h
      exact h.symm
    have h := hσ (σ⁻¹ x) hy
    rw [hcancel, hval, w.valuation.map_sub_swap] at h
    exact h

/-- A prime different from the actual residue characteristic is a unit
in the original valuation subring, not a supplied order-exclusion fact. -/
theorem prime_unit_of_ne_residue_char (w : ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField w) p] (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    IsUnit (q : w) := by
  have hnot : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with hp | hp
    · exact (Fact.out : p.Prime).ne_one hp
    · exact hqp hp.symm
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (q : w)).mp
  rw [map_natCast]
  exact (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField w) p q).not.mpr hnot

/-- The finite actual wild-displacement subgroup is a p-group for its
actual positive residue characteristic. No p-group action is a hypothesis. -/
theorem strictDisplacementGroup_isPGroup [FiniteDimensional K L]
    (w : ValuationSubring L) (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField w) p] :
    IsPGroup p (strictDisplacementGroup (K := K) w) := by
  classical
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  haveI : Finite (strictDisplacementGroup (K := K) w) := inferInstance
  apply (isPGroup_iff_primeFactors_card_subset (G := strictDisplacementGroup (K := K) w)
    (Fact.out : p.Prime).ne_zero).mpr
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdiv : q ∣ Nat.card (strictDisplacementGroup (K := K) w) := Nat.dvd_of_mem_primeFactors hq
  by_cases hqp : q = p
  · subst q
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
  · have hu := prime_unit_of_ne_residue_char w p q hqprime hqp
    have hvq : w.valuation (q : L) = 1 := (w.valuation_eq_one_iff (q : w)).mp hu
    obtain ⟨σ, hσorder⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqprime⟩) hqdiv
    have horder : orderOf (σ : L ≃ₐ[K] L) = q := (Subgroup.orderOf_coe σ).trans hσorder
    have hσstrict : ∀ x : L, x ≠ 0 →
        w.valuation ((σ : L ≃ₐ[K] L) x - x) < w.valuation x := σ.2
    have hcop : Nat.Coprime (orderOf (σ : L ≃ₐ[K] L)) q :=
      WildTrace.orderOf_coprime_unit_prime w.valuation (σ : L ≃ₐ[K] L) hσstrict
        (isOfFinOrder_of_finite _) q hqprime hvq
    have hn := (hqprime.coprime_iff_not_dvd).mp hcop.symm
    exact False.elim (hn (horder.symm ▸ dvd_rfl))

end WildFiniteGroup
