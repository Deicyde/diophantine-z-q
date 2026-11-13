import ZInQKernel.Contrib.LocalSquareRoot.FiniteLevel
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# Cyclotomic fields produced by the actual local-Kronecker-Weber hypothesis

The field and normalization proofs are ported from
`scratch/glue-sqrt-disj/Disj.lean`, revision
`533aa66cc3485e21f2d90303e3a34f79d081722d`, lines 1029-1087.
Unlike the research file, this module imports the baseline `PkgI6.LocalKroneckerWeber`;
it neither redeclares that proposition nor supplies a proof of it.
-/

namespace ZInQ.Contrib.LocalSquareRoot
namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℚ_p(μ_n) ⊆ \bar ℚ_p`. -/
noncomputable abbrev muField (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}

/-- `ℚ_p(μ_n) ⊆ \bar ℚ_p` is an `n`-th cyclotomic extension of `ℚ_p`. -/
theorem isCyclotomicExtension_muField (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ_[p] (muField p n) := by
  have hn : NeZero ((n : ℕ) : PadicAlgCl p) := NeZero.charZero
  have h := IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot {n} ℚ_[p]
    (L := PadicAlgCl p) (fun n' hn' _ => by
      rw [Set.mem_singleton_iff] at hn'
      subst hn'
      exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) n')
  have hset : {b : PadicAlgCl p | ∃ n' ∈ ({n} : Set ℕ), n' ≠ 0 ∧ b ^ n' = 1} =
      {x : PadicAlgCl p | x ^ n = 1} := by
    ext b
    simp [NeZero.ne n]
  rw [hset] at h
  exact h

/-- Levels are monotone: `ℚ_p(μ_a) ≤ ℚ_p(μ_b)` when `a ∣ b`. -/
theorem muField_mono {a b : ℕ} (hab : a ∣ b) : muField p a ≤ muField p b := by
  apply IntermediateField.adjoin.mono
  intro x hx
  obtain ⟨c, rfl⟩ := hab
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [pow_mul, hx, one_pow]

/-- **I6.3, normalized.** Under local Kronecker–Weber, every finite abelian `M ⊆ \bar ℚ_p` lies in
`ℚ_p(μ_{p^k m})` for some `k` and some `m ≥ 1` prime to `p`. -/
theorem le_muField_of_lkw (hLKW : PkgI6.LocalKroneckerWeber p)
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    [IsAbelianGalois ℚ_[p] M] :
    ∃ k m : ℕ, 0 < m ∧ p.Coprime m ∧ M ≤ muField p (p ^ k * m) := by
  obtain ⟨n, hn, hM⟩ := hLKW M inferInstance inferInstance
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.one_lt.ne'
  refine ⟨e, m, Nat.pos_of_ne_zero ?_, (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm, hM⟩
  rintro rfl
  simp at hn

/-- The bigger level used by the criterion: `p^k m ∣ p^{k+1} (p^{2f} - 1)`, `f = ord_m(p)`, so
`ℚ_p(μ_{p^k m}) ≤ ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`. -/
theorem muField_le_level (k m : ℕ) (hcop : p.Coprime m) :
    muField p (p ^ k * m) ≤
      muField p (p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1)) := by
  apply muField_mono
  apply Nat.mul_dvd_mul (pow_dvd_pow p (Nat.le_succ k))
  -- `m ∣ p^{2f} - 1`
  have h := pow_orderOf_eq_one (ZMod.unitOfCoprime p hcop)
  have h' : (ZMod.unitOfCoprime p hcop) ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) = 1 := by
    rw [pow_mul', h, one_pow]
  have hd1 : 1 ≤ p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) :=
    Nat.one_le_pow _ _ hp.out.pos
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow] at h'
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one]
  exact h'


instance neZero_prime (p : ℕ) [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ_[p] (muField p n) :=
  isCyclotomicExtension_muField p n

instance (n : ℕ) [NeZero n] : FiniteDimensional ℚ_[p] (muField p n) :=
  IsCyclotomicExtension.finiteDimensional {n} ℚ_[p] _

instance (n : ℕ) [NeZero n] : IsGalois ℚ_[p] (muField p n) :=
  IsCyclotomicExtension.isGalois {n} ℚ_[p] _

/-- The arithmetic level divisibility; no additional typeclass premise is retained. -/
theorem level_dvd (k m : ℕ) (hcop : p.Coprime m) :
    p ^ k * m ∣ p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1) :=
  Nat.mul_dvd_mul (pow_dvd_pow p (Nat.le_succ k)) (dvd_pow_orderOf_sub_one hcop 2)

/-- The enlarged prime-to-p level is nonzero, including when `m = 1`. -/
theorem enlarged_level_pos (m : ℕ) [NeZero m] (hcop : p.Coprime m) :
    0 < p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1 := by
  have hf : 0 < orderOf (ZMod.unitOfCoprime p hcop) := orderOf_pos _
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow : p ≤ p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) :=
    Nat.le_self_pow (by omega) p
  omega

end GlueSqrtDisj
end ZInQ.Contrib.LocalSquareRoot
