import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Prime Hecke rationality: first mathematical constructions

Target: `CoeffRational.HeckePrimeIntegralToRational` at the recorded base.
These theorems prove actual coefficient statements for the actual Hecke
operator. They do NOT yet prove that full all-level leaf: the identity-diamond
hypothesis below is a restriction, explicitly visible in the statement.

No target definition, existing theorem, dependency pin or assembly is changed.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}

/-- Coefficients away from multiples of p are rational with no diamond-action
premise. The original rational witness is the integral input coefficient. -/
theorem rational_coeff_off_prime_multiples
    (hp : p.Prime) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ))
    (m : ℕ) (hm : ¬ p ∣ m) :
    ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g m,
    if_neg hm, add_zero]
  obtain ⟨z, hz⟩ := hg (p * m)
  exact ⟨(z : ℚ), by simpa using hz⟩

/-- In the identity diamond class the actual zero-extended diamond operator
is the identity, not a separately assumed rationality theorem. -/
theorem diamond_prime_eq_self_of_unit_eq_one
    (hcop : Nat.Coprime p N) (hunit : ZMod.unitOfCoprime p hcop = 1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOpCuspNat k p g = g := by
  rw [diamondOpCuspNat_of_coprime k hcop, hunit, diamondOpCusp_one,
    LinearMap.id_apply]

/-- A genuine all-coefficient special case of the claimed leaf. This works
for every weight; the full leaf's k ≥ 2 hypothesis is therefore not needed
in this restricted diamond class. The extra unit condition is NOT hidden. -/
theorem rational_hecke_of_unit_eq_one
    (hp : p.Prime) (hcop : Nat.Coprime p N)
    (hunit : ZMod.unitOfCoprime p hcop = 1)
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
  · rw [diamond_prime_eq_self_of_unit_eq_one hcop hunit]
    obtain ⟨z₂, hz₂⟩ := hg (m / p)
    refine ⟨(z₁ : ℚ) + (p : ℚ) ^ (k - 1) * (z₂ : ℚ), ?_⟩
    rw [hz₂]
    push_cast
    ring
  · exact ⟨(z₁ : ℚ), by simp⟩

/-- The residue-class formulation, directly in the same ZMod N used by the
canonical operator. No alternative notion of a prime or level is introduced. -/
theorem rational_hecke_of_prime_eq_one
    (hp : p.Prime) (hcop : Nat.Coprime p N) (hclass : (p : ZMod N) = 1)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  apply rational_hecke_of_unit_eq_one hp hcop _ g hg
  apply Units.ext
  simpa using hclass

/-- At level one every unit is the identity: no diamond-preservation
premise survives in this concrete level-one theorem. This is NOT the full
all-level statement. -/
theorem rational_hecke_level_one
    (k : ℤ) (p : ℕ) (hp : p.Prime)
    (g : CuspForm ((Gamma1 1).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 1 p) g)).coeff m =
        (q : ℂ) := by
  apply rational_hecke_of_unit_eq_one hp (Nat.coprime_one_right p) _ g hg
  exact Subsingleton.elim _ _

end ZInQ.Contrib.HeckePrimeRationality
