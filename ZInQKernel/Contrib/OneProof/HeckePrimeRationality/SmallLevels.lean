import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.NegOne

/-!
# Complete prime-Hecke rationality at the five sign-only levels

This file proves the target's entire conclusion at N = 1, 2, 3, 4, 6.
The level restriction is explicit: this is NOT a proof of the all-level
`CoeffRational.HeckePrimeIntegralToRational` leaf. All input forms, prime
Hecke operators, coefficient maps and good-prime conditions are unchanged.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

-- These four decisions are closed theorems, outside any variable-dependent
-- typeclass context. The general theorem below applies them after substituting
-- N; no local free variable is passed to the kernel decision check.
private theorem units_sign_two : ∀ d : (ZMod 2)ˣ, d = 1 ∨ d = -1 := by
  decide +kernel

private theorem units_sign_three : ∀ d : (ZMod 3)ˣ, d = 1 ∨ d = -1 := by
  decide +kernel

private theorem units_sign_four : ∀ d : (ZMod 4)ˣ, d = 1 ∨ d = -1 := by
  decide +kernel

private theorem units_sign_six : ∀ d : (ZMod 6)ˣ, d = 1 ∨ d = -1 := by
  decide +kernel

variable {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}

/-- A finite, kernel-reducible classification at the five concrete levels.
No mathematical statement about arbitrary units or levels is assumed. -/
theorem units_sign_of_small_level
    (hN : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 6) :
    ∀ d : (ZMod N)ˣ, d = 1 ∨ d = -1 := by
  rcases hN with h1 | h2 | h3 | h4 | h6
  · subst N
    intro d
    exact Or.inl (Subsingleton.elim _ _)
  · subst N
    exact units_sign_two
  · subst N
    exact units_sign_three
  · subst N
    exact units_sign_four
  · subst N
    exact units_sign_six

/-- The actual prime-Hecke conclusion once the unit group consists of sign
classes. The finite algebraic hypothesis is exposed, not an unproved
rationality assumption inserted into the claimed all-level theorem. -/
theorem rational_hecke_of_units_sign
    (hN : ∀ d : (ZMod N)ˣ, d = 1 ∨ d = -1)
    (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  have hcop : Nat.Coprime p N := (hp.coprime_iff_not_dvd).mpr hpN
  rcases hN (ZMod.unitOfCoprime p hcop) with hpos | hneg
  · exact rational_hecke_of_unit_eq_one hp hcop hpos g hg
  · exact rational_hecke_of_unit_eq_neg_one hp hcop hneg g hg

/-- A checked construction for every input form and every good prime at
these five levels. No caller Hecke/diamond theorem or Name-like surrogate
is supplied. The full all-level leaf remains open outside this condition. -/
theorem rational_hecke_small_levels
    (hN : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 6)
    (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) :=
  rational_hecke_of_units_sign (units_sign_of_small_level hN) hp hpN g hg

end ZInQ.Contrib.HeckePrimeRationality
