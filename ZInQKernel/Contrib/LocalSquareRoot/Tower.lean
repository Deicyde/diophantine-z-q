import ZInQKernel.Contrib.LocalSquareRoot.Fields
import ZInQKernel.Contrib.LocalSquareRoot.GaloisQuotient

/-!
# Actual inclusions and level bookkeeping

All algebras in a cyclotomic tower below are induced by the inclusion of intermediate fields
in the same fixed algebraic closure. No alternative embedding or target hypothesis is used.
-/

namespace ZInQ.Contrib.LocalSquareRoot

/-- The algebra of an actual inclusion of intermediate fields in the same ambient field. -/
noncomputable def fieldInclusionAlgebra {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K L : IntermediateField F Ω) (hKL : K ≤ L) : Algebra K L :=
  (IntermediateField.inclusion hKL).toRingHom.toAlgebra

/-- The inclusion algebra commutes with the base-field maps. -/
theorem fieldInclusion_scalarTower_base {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K L : IntermediateField F Ω) (hKL : K ≤ L) :
    letI : Algebra K L := fieldInclusionAlgebra K L hKL
    IsScalarTower F K L := by
  letI : Algebra K L := fieldInclusionAlgebra K L hKL
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The inclusion algebra commutes with the maps to the actual ambient field. -/
theorem fieldInclusion_scalarTower_top {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K L : IntermediateField F Ω) (hKL : K ≤ L) :
    letI : Algebra K L := fieldInclusionAlgebra K L hKL
    IsScalarTower K L Ω := by
  letI : Algebra K L := fieldInclusionAlgebra K L hKL
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Restriction through an inclusion has precisely the same action on the original field. -/
theorem restrictNormal_inclusion_trans {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (K L : IntermediateField F Ω) (hKL : K ≤ L) [Normal F K] [Normal F L]
    (g : Gal(Ω/F)) :
    letI : Algebra K L := fieldInclusionAlgebra K L hKL
    letI : IsScalarTower F K L := fieldInclusion_scalarTower_base K L hKL
    (g.restrictNormal L).restrictNormal K = g.restrictNormal K := by
  letI : Algebra K L := fieldInclusionAlgebra K L hKL
  letI : IsScalarTower F K L := fieldInclusion_scalarTower_base K L hKL
  letI : IsScalarTower K L Ω := fieldInclusion_scalarTower_top K L hKL
  exact restrictNormal_trans g

/-- The canonical decomposition uses exactly the factorization and casts in the baseline leaf. -/
theorem canonical_cyclotomic_level (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N] :
    0 < N / p ^ N.factorization p ∧
      p.Coprime (N / p ^ N.factorization p) ∧
      N = p ^ N.factorization p * (N / p ^ N.factorization p) :=
  ⟨Nat.ordCompl_pos p (NeZero.ne N), Nat.coprime_ordCompl hp.out (NeZero.ne N),
    (Nat.ordProj_mul_ordCompl_eq_self N p).symm⟩

/-- Divisibility of normalized cyclotomic levels gives both required component maps. -/
theorem normalized_level_dvd (p : ℕ) [hp : Fact p.Prime]
    (k m k' m' : ℕ) [NeZero m] [NeZero m']
    (hcop : p.Coprime m) (hcop' : p.Coprime m')
    (hdiv : p ^ k * m ∣ p ^ k' * m') : k ≤ k' ∧ m ∣ m' := by
  have hm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop
  have hm' : ¬ p ∣ m' := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop'
  have hfa : (p ^ k * m).factorization p = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m),
      Finsupp.add_apply, Nat.factorization_pow_self hp.out,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  have hfb : (p ^ k' * m').factorization p = k' := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m'),
      Finsupp.add_apply, Nat.factorization_pow_self hp.out,
      Nat.factorization_eq_zero_of_not_dvd hm', add_zero]
  have hfact := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m))
    (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m'))).mpr hdiv
  have hk : k ≤ k' := by
    simpa only [hfa, hfb] using hfact p
  have hmdiv : m ∣ p ^ k * m := ⟨p ^ k, mul_comm _ _⟩
  have hmcompl := Nat.dvd_ordCompl_of_dvd_not_dvd (hmdiv.trans hdiv) hm
  have hmm' : m ∣ m' := by
    simpa only [Nat.ordCompl_pow_mul_of_not_dvd k' hp.out hm'] using hmcompl
  exact ⟨hk, hmm'⟩

end ZInQ.Contrib.LocalSquareRoot
