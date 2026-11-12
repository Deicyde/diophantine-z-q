import Mathlib

/-!
# glue-sqrt-local: the `p`-power cyclotomic extension of `ℚ_p`

`Φ_{p^{n+1}}` is irreducible over `ℚ_p` (Eisenstein at `p` after `X ↦ X + 1`), so the Galois
group of any `p^{n+1}`-th cyclotomic extension of `ℚ_p` is `(ℤ/p^{n+1})ˣ` (Mathlib's
`IsCyclotomicExtension.autEquivPow`).
-/

open Polynomial

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime]

/-- `Φ_{p^{n+1}}(X + 1)` is Eisenstein at the maximal ideal `(p)` of `ℤ_p`. -/
theorem cyclotomic_prime_pow_comp_isEisensteinAt_padicInt (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hZ := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hmap : (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1) =
      ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) := by
    simp [map_comp]
  have hne : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PadicInt.p_nonunit
  rw [hmap]
  refine Monic.isEisensteinAt_of_mem_of_notMem ?_ hne ?_ ?_
  · refine Monic.map _ ?_
    rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
    refine (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) fun h => ?_
    rw [natDegree_X_add_C] at h
    exact zero_ne_one h.symm
  · intro i hi
    rw [coeff_map]
    have hi' : i < ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).natDegree := by
      rwa [natDegree_map_eq_of_injective (RingHom.injective_int _)] at hi
    have hm := hZ.mem hi'
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    rw [Ideal.mem_span_singleton]
    exact ⟨(c : ℤ_[p]), by rw [hc]; simp⟩
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
      eval_one_cyclotomic_prime_pow]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : (p : ℤ_[p]) * (1 - p * c) = 0 := by
      simp only [map_natCast] at hc
      linear_combination hc
    rcases mul_eq_zero.mp h1 with h | h
    · exact hp.out.ne_zero (by exact_mod_cast h)
    · apply PadicInt.p_nonunit (p := p)
      exact IsUnit.of_mul_eq_one c (by linear_combination -h)

/-- **`Φ_{p^{n+1}}` is irreducible over `ℚ_p`.** -/
theorem cyclotomic_prime_pow_irreducible_padic (n : ℕ) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
  have hE := cyclotomic_prime_pow_comp_isEisensteinAt_padicInt p n
  have hmon : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    rw [show (X + 1 : ℤ_[p][X]) = X + C 1 by simp]
    refine (cyclotomic.monic _ ℤ_[p]).comp (monic_X_add_C 1) fun h => ?_
    rw [natDegree_X_add_C] at h
    exact zero_ne_one h.symm
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)]
    exact PadicInt.prime_p
  have hdeg : 0 < ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, natDegree_cyclotomic]
    simp only [show (X + 1 : ℤ_[p][X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
    exact Nat.totient_pos.mpr (pow_pos hp.out.pos _)
  have hirr := hE.irreducible hprime hmon.isPrimitive hdeg
  have hirrQ := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr
  have hmapQ : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).map (algebraMap ℤ_[p] ℚ_[p]) =
      algEquivAevalXAddC (1 : ℚ_[p]) (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
    rw [map_comp, map_cyclotomic]
    simp [algEquivAevalXAddC, ← comp_eq_aeval]
  rw [hmapQ] at hirrQ
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hirrQ

end GlueSqrtLocal

#print axioms GlueSqrtLocal.cyclotomic_prime_pow_irreducible_padic
