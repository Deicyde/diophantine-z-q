import ZInQKernel.Contrib.OneProof.HeckePrimeRationality
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity

/-!
# Prime Hecke rationality in the negative-identity diamond class

The actual diamond operator at -1 acts by (-1)^k. This yields rational
coefficients from integral input without assuming a general diamond-preservation
leaf. The residue/unit restriction is explicit; this is still NOT the full
all-level `CoeffRational.HeckePrimeIntegralToRational` theorem.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}

/-- The nontrivial sign class is genuinely controlled by the -I action.
No unproved rationality premise for all diamond operators is supplied. -/
theorem rational_diamond_coeff_of_unit_eq_neg_one
    (hcop : Nat.Coprime p N) (hunit : ZMod.unitOfCoprime p hcop = -1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (diamondOpCuspNat k p g)).coeff m = (q : ℂ) := by
  intro m
  rw [diamondOpCuspNat_of_coprime k hcop, hunit, TauCeti.diamondOpCusp_neg_one,
    FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, smul_eq_mul]
  obtain ⟨z, hz⟩ := hg m
  rw [hz]
  refine ⟨(-1 : ℚ) ^ k * (z : ℚ), ?_⟩
  push_cast
  ring

/-- All coefficients of T_p in the negative-identity diamond class. The
actual double-coset operator and normalization are retained. -/
theorem rational_hecke_of_unit_eq_neg_one
    (hp : p.Prime) (hcop : Nat.Coprime p N)
    (hunit : ZMod.unitOfCoprime p hcop = -1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  intro m
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g m]
  obtain ⟨z₁, hz₁⟩ := hg (p * m)
  rw [hz₁]
  split_ifs with hpm
  · obtain ⟨q₂, hq₂⟩ := rational_diamond_coeff_of_unit_eq_neg_one hcop hunit g hg (m / p)
    refine ⟨(z₁ : ℚ) + (p : ℚ) ^ (k - 1) * q₂, ?_⟩
    rw [hq₂]
    push_cast
    ring
  · exact ⟨(z₁ : ℚ), by simp⟩

/-- The sign-class statement directly in ZMod N. -/
theorem rational_hecke_of_prime_eq_neg_one
    (hp : p.Prime) (hcop : Nat.Coprime p N) (hclass : (p : ZMod N) = -1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  apply rational_hecke_of_unit_eq_neg_one hp hcop _ g hg
  apply Units.ext
  simpa using hclass

/-- The union of the two checked residue classes. This is a substantial
specialization, not an elimination of the residue condition from the leaf. -/
theorem rational_hecke_of_prime_sign_class
    (hp : p.Prime) (hcop : Nat.Coprime p N)
    (hclass : (p : ZMod N) = 1 ∨ (p : ZMod N) = -1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  rcases hclass with hpos | hneg
  · exact rational_hecke_of_prime_eq_one hp hcop hpos g hg
  · exact rational_hecke_of_prime_eq_neg_one hp hcop hneg g hg

end ZInQ.Contrib.HeckePrimeRationality
