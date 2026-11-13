import ZInQKernel.Contrib.Abhyankar.Local
import ZInQKernel.Contrib.Abhyankar.Model

/-!
# Constructing the tame model from actual uniformizers and indices

The exponent in the uniformizer factorization is identified with Mathlib's
localization-length index. The quotient `d` and the unit root
`y = t^d / ϖ` are constructed from the divisibility hypothesis, not assumed.
The local DVR and nonzero base embedding inputs are supplied by `Primes.lean`
for the integral closures in the baseline.
-/

namespace ZInQ.Contrib.Abhyankar

open IsLocalRing IsDiscreteValuationRing

/-- A base uniformizer factors using the actual prime ramification index. -/
theorem uniformizer_factorization_at_prime
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] {π : R} (hπ : Irreducible π)
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)]
    [IsDomain (Localization.AtPrime Q)] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    (hπQ : algebraMap R (Localization.AtPrime Q) π ≠ 0) :
    ∃ (ϖ : Localization.AtPrime Q) (u : (Localization.AtPrime Q)ˣ),
      Irreducible ϖ ∧ algebraMap R (Localization.AtPrime Q) π =
        (u : Localization.AtPrime Q) * ϖ ^ Q.ramificationIdx R := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible (Localization.AtPrime Q)
  obtain ⟨e, u, hu⟩ := eq_unit_mul_pow_irreducible hπQ hϖ
  have hval := addVal_algebraMap_uniformizer hπ Q hπQ
  rw [hu, addVal_def' u hϖ e, ENat.natCast_inj] at hval
  exact ⟨ϖ, u, hϖ, hval ▸ hu⟩

/-- The field calculation behind the tame unit-root construction. -/
theorem div_root_relations
    {M : Type*} [Field M] {a u t : M} (ha : a ≠ 0) {e d : ℕ}
    (ht : t ^ (e * d) = u * a ^ e) :
    (t ^ d / a) ^ e = u ∧ t ^ d = a * (t ^ d / a) := by
  constructor
  · rw [div_pow, ← pow_mul, Nat.mul_comm d e, ht,
      mul_div_cancel_right₀ _ (pow_ne_zero _ ha)]
  · field_simp

/-- **Constructed local-model data.** From the unit index, index divisibility,
and the actual root equation, construct the uniformizer, unit, quotient
exponent and unit root satisfying the model equations. -/
theorem exists_tameModel_data
    {R S M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] [Field M] [Algebra R M]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)]
    [IsDomain (Localization.AtPrime Q)] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    [Algebra (Localization.AtPrime Q) M] [IsScalarTower R (Localization.AtPrime Q) M]
    [FaithfulSMul (Localization.AtPrime Q) M]
    {π : R} (hπ : Irreducible π)
    (hπQ : algebraMap R (Localization.AtPrime Q) π ≠ 0)
    {n : ℕ} (hn : 0 < n) (heunit : IsUnit ((Q.ramificationIdx R : ℕ) : R))
    (hediv : Q.ramificationIdx R ∣ n) {t : M}
    (ht : t ^ n = algebraMap R M π) :
    ∃ (ϖ : Localization.AtPrime Q) (u : (Localization.AtPrime Q)ˣ) (d : ℕ) (y : M),
      Irreducible ϖ ∧ 0 < Q.ramificationIdx R ∧ 0 < d ∧ n = Q.ramificationIdx R * d ∧
      IsUnit ((Q.ramificationIdx R : ℕ) : Localization.AtPrime Q) ∧
      y ^ Q.ramificationIdx R = algebraMap (Localization.AtPrime Q) M (u : Localization.AtPrime Q) ∧
      t ^ d = algebraMap (Localization.AtPrime Q) M ϖ * y := by
  let B := Localization.AtPrime Q
  obtain ⟨ϖ, u, hϖ, hfactor⟩ := uniformizer_factorization_at_prime hπ Q hπQ
  obtain ⟨d, hnd⟩ := hediv
  have hepos : 0 < Q.ramificationIdx R := Nat.pos_of_ne_zero fun he0 ↦
    heunit.ne_zero (by simp [he0])
  have heB : IsUnit ((Q.ramificationIdx R : ℕ) : B) := by
    simpa only [map_natCast] using heunit.map (algebraMap R B)
  have hd : 0 < d := Nat.pos_of_ne_zero fun hd0 ↦ hn.ne' (by simpa [hd0] using hnd)
  have hϖM : algebraMap B M ϖ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B M)).mpr hϖ.ne_zero
  have hpower : t ^ (Q.ramificationIdx R * d) =
      algebraMap B M (u : B) * algebraMap B M ϖ ^ Q.ramificationIdx R := by
    rw [← hnd, ht, IsScalarTower.algebraMap_apply R B M, hfactor, map_mul, map_pow]
  obtain ⟨hy, hty⟩ := div_root_relations hϖM hpower
  exact ⟨ϖ, u, d, t ^ d / algebraMap B M ϖ, hϖ, hepos, hd, hnd, heB, hy, hty⟩

end ZInQ.Contrib.Abhyankar
