import ZInQKernel.Contrib.OneProof.RC.Intertwine.Characters
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-! The finite character over the rationals, by adding one rational fractional
part per nonintegral place (on-the-spot (c), tex 8640–8642). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open scoped BigOperators RestrictedProduct

abbrev Place := {p : ℕ // p.Prime}

instance (p : Place) : Fact p.val.Prime := ⟨p.property⟩

abbrev RationalFiniteAdeles :=
  RestrictedProduct (fun p : Place => ℚ_[p.val])
    (fun p => (PadicInt.subring p.val : Set ℚ_[p.val])) Filter.cofinite

def integralAdeles : Subring RationalFiniteAdeles where
  carrier := {x | ∀ p : Place, x p ∈ PadicInt.subring p.val}
  zero_mem' := fun p => (PadicInt.subring p.val).zero_mem
  one_mem' := fun p => (PadicInt.subring p.val).one_mem
  add_mem' hx hy := fun p => (PadicInt.subring p.val).add_mem (hx p) (hy p)
  mul_mem' hx hy := fun p => (PadicInt.subring p.val).mul_mem (hx p) (hy p)
  neg_mem' hx := fun p => (PadicInt.subring p.val).neg_mem (hx p)

theorem rat_mem_at (q : ℚ) (p : Place) (h : ¬p.val ∣ q.den) :
    (q : ℚ_[p.val]) ∈ PadicInt.subring p.val := by
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  change ‖(q.num : ℚ_[p.val]) / q.den‖ ≤ 1
  rw [norm_div, Padic.norm_natCast_eq_one_iff.mpr ((p.property.coprime_iff_not_dvd).mpr h),
    div_one]
  exact (intCast_mem (PadicInt.subring p.val) q.num)

def diagonalRat : ℚ →+* RationalFiniteAdeles where
  toFun q := RestrictedProduct.mk (fun p => (q : ℚ_[p.val])) (by
    rw [Filter.eventually_cofinite]
    have hf : {p : Place | p.val ∣ q.den}.Finite :=
      (Set.finite_Iic q.den).preimage Subtype.val_injective.injOn |>.subset
        (fun p hp => Nat.le_of_dvd (Nat.pos_of_ne_zero q.den_ne_zero) hp)
    exact hf.subset fun p hp => not_not.mp fun hn => hp (rat_mem_at q p hn))
  map_zero' := by ext p; exact Rat.cast_zero
  map_one' := by ext p; exact Rat.cast_one
  map_add' q r := by ext p; exact Rat.cast_add q r
  map_mul' q r := by ext p; exact Rat.cast_mul q r

instance : Algebra ℚ RationalFiniteAdeles := diagonalRat.toAlgebra

theorem diagonal_apply (q : ℚ) (p : Place) :
    (algebraMap ℚ RationalFiniteAdeles q) p = (q : ℚ_[p.val]) := rfl

theorem rational_integral (q : ℚ) :
    algebraMap ℚ RationalFiniteAdeles q ∈ integralAdeles ↔ ∃ z : ℤ, q = z := by
  constructor
  · intro h
    have hd : q.den = 1 := by
      by_contra hd
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
      letI : Fact p.Prime := ⟨hp⟩
      have hn : ¬p ∣ q.num.natAbs := fun hm =>
        hp.not_dvd_one (q.reduced.gcd_eq_one ▸ Nat.dvd_gcd hm hpd)
      have hi : ‖(q : ℚ_[p])‖ ≤ 1 := h ⟨p, hp⟩
      rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
        norm_div] at hi
      have hc : IsCoprime q.num (p : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
        exact ((hp.coprime_iff_not_dvd).mpr hn).symm.gcd_eq_one
      rw [Padic.norm_intCast_eq_one_iff.mpr hc] at hi
      have hlt := (Padic.norm_natCast_lt_one_iff (p := p)).mpr hpd
      have hpos : (0 : ℝ) < ‖(q.den : ℚ_[p])‖ := norm_pos_iff.mpr
        (Nat.cast_ne_zero.mpr q.den_ne_zero)
      have := (div_le_iff₀ hpos).mp hi
      linarith
    exact ⟨q.num, by rw [← Rat.num_div_den q, hd]; simp⟩
  · rintro ⟨z, rfl⟩ p
    simpa only [diagonal_apply, Rat.cast_intCast] using intCast_mem (PadicInt.subring p.val) z

theorem exists_local_fraction (p : Place) (x : ℚ_[p.val]) :
    ∃ n k : ℕ, k < p.val ^ n ∧ x - (((k : ℚ) / (p.val : ℚ)^n : ℚ) : ℚ_[p.val]) ∈ PadicInt.subring p.val := by
  have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p.val (ε := (‖x‖ + 1)⁻¹) (by positivity)
  have he : ‖(p.val : ℚ_[p.val]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have hl : (p.val : ℝ) ^ (-(n : ℤ)) * (‖x‖ + 1) < 1 :=
      (lt_div_iff₀ (by positivity)).mp (by rw [one_div]; exact hn)
    nlinarith [zpow_pos (Nat.cast_pos.mpr p.property.pos : (0 : ℝ) < p.val) (-(n : ℤ))]
  let y : ℤ_[p.val] := ⟨_, he⟩
  refine ⟨n, y.appr n, y.appr_lt n, ?_⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n y)
  have hv' := congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hv
  push_cast at hv'
  change (p.val : ℚ_[p.val]) ^ n * x - (y.appr n : ℚ_[p.val]) =
    (p.val : ℚ_[p.val]) ^ n * (v : ℚ_[p.val]) at hv'
  have heq : x - (((y.appr n : ℚ) / (p.val : ℚ)^n : ℚ) : ℚ_[p.val]) = v := by
    push_cast
    field_simp
    linear_combination hv'
  rw [heq]
  exact v.property

theorem prime_fraction_integral_elsewhere {p t : Place} (h : t ≠ p) (k n : ℕ) :
    (((k : ℚ) / (p.val : ℚ)^n : ℚ) : ℚ_[t.val]) ∈ PadicInt.subring t.val := by
  have hd : ¬ t.val ∣ p.val := fun hd =>
    h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq t.property p.property).mp hd))
  push_cast
  change ‖(k : ℚ_[t.val]) / (p.val : ℚ_[t.val]) ^ n‖ ≤ 1
  rw [norm_div, norm_pow,
    Padic.norm_natCast_eq_one_iff.mpr ((t.property.coprime_iff_not_dvd).mpr hd), one_pow, div_one]
  exact natCast_mem (PadicInt.subring t.val) k

def localFraction (p : Place) (x : ℚ_[p.val]) : ℚ := by
  classical
  exact if x ∈ PadicInt.subring p.val then 0 else
    ((exists_local_fraction p x).choose_spec.choose : ℚ) /
      (p.val : ℚ)^((exists_local_fraction p x).choose)

theorem localFraction_spec (p : Place) (x : ℚ_[p.val]) :
    x - (localFraction p x : ℚ_[p.val]) ∈ PadicInt.subring p.val := by
  unfold localFraction
  split_ifs with h
  · simpa using h
  · exact (exists_local_fraction p x).choose_spec.choose_spec.2

theorem localFraction_elsewhere {p t : Place} (h : t ≠ p) (x : ℚ_[p.val]) :
    (localFraction p x : ℚ_[t.val]) ∈ PadicInt.subring t.val := by
  unfold localFraction
  split_ifs
  · simp
  · exact prime_fraction_integral_elsewhere h _ _

theorem sum_localFraction_spec (x : RationalFiniteAdeles) (S : Finset Place)
    (hS : ∀ p, p ∉ S → x p ∈ PadicInt.subring p.val) :
    x - algebraMap ℚ RationalFiniteAdeles (∑ p ∈ S, localFraction p (x p)) ∈ integralAdeles := by
  classical
  intro t
  change x t - (↑(∑ p ∈ S, localFraction p (x p)) : ℚ_[t.val]) ∈ PadicInt.subring t.val
  rw [Rat.cast_sum]
  by_cases ht : t ∈ S
  · rw [← Finset.sum_erase_add _ _ ht, add_comm (∑ p ∈ S.erase t, _), ← sub_sub]
    exact (PadicInt.subring t.val).sub_mem (localFraction_spec t (x t))
      ((PadicInt.subring t.val).sum_mem fun p hp => localFraction_elsewhere
        (Ne.symm (Finset.ne_of_mem_erase hp)) (x p))
  · exact (PadicInt.subring t.val).sub_mem (hS t ht)
      ((PadicInt.subring t.val).sum_mem fun p hp => localFraction_elsewhere
        (p := p) (t := t) (fun h => ht (by simpa [h] using hp)) (x p))

/-- Finite rational approximation modulo the integral adèles. -/
theorem rationalFiniteModel : IntegralModel integralAdeles where
  rat_mem := rational_integral
  approx x := by
    classical
    have H : ∀ᶠ p : Place in Filter.cofinite, x p ∈ PadicInt.subring p.val := x.2
    rw [Filter.eventually_cofinite] at H
    let S := H.toFinset
    exact ⟨_, sum_localFraction_spec x S fun p hp => by
      by_contra hn
      exact hp (H.mem_toFinset.mpr hn)⟩

/-- The finite character is the product of the actual local fractional-part
characters on any finite set containing the nonintegral components. -/
theorem finitePhase_local_product (x : RationalFiniteAdeles) (S : Finset Place)
    (hS : ∀ p, p ∉ S → x p ∈ PadicInt.subring p.val) :
    finitePhase rationalFiniteModel x = ∏ p ∈ S, rationalPhase (localFraction p (x p)) :=
  finitePhase_eq_product rationalFiniteModel S _ (sum_localFraction_spec x S hS)

#print axioms rat_mem_at
#print axioms diagonal_apply
#print axioms rational_integral
#print axioms exists_local_fraction
#print axioms prime_fraction_integral_elsewhere
#print axioms localFraction_spec
#print axioms localFraction_elsewhere
#print axioms sum_localFraction_spec
#print axioms rationalFiniteModel
#print axioms finitePhase_local_product

end ZInQ.Manuscript.RC.Intertwine
