import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RealCoefficients

/-!
# Rational Hecke coefficients on a single character component

A nonzero cusp form with real Fourier coefficients determines a character
fixed by inversion. Its actual diamond eigenvalues are therefore signs.
For an integral Fourier expansion this gives integral prime-Hecke output
at every positive level, without an arithmetic spanning hypothesis.

The character-space restriction is essential: this does not assert that
an arbitrary integral cusp form belongs to a single character space.
-/

noncomputable section
set_option autoImplicit false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm

namespace DirectHeckeCharacter

open ZInQ.Contrib.HeckePrimeRationality

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A nonzero real-coefficient cusp form has an inversion-fixed nebentypus. -/
theorem character_eq_inverse_of_real
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hχ : g ∈ cuspFormCharSpace k χ) (hg0 : g ≠ 0)
    (hg : HasRealQExpansion g) : χ = χ⁻¹ := by
  have hχ' := CuspForm.conj_mem_cuspFormCharSpace hχ
  rw [conjugate_eq_self_of_real_qExpansion g hg] at hχ'
  exact eq_of_mem_cuspFormCharSpace_of_ne_zero hχ hχ' hg0

/-- Every diamond eigenvalue of that actual form is either one or minus one. -/
theorem character_value_sign_of_real
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hχ : g ∈ cuspFormCharSpace k χ) (hg0 : g ≠ 0)
    (hg : HasRealQExpansion g) (d : (ZMod N)ˣ) :
    (χ d : ℂ) = 1 ∨ (χ d : ℂ) = -1 := by
  have hχinv := character_eq_inverse_of_real χ g hχ hg0 hg
  have hd : (χ d : ℂ) = (χ d : ℂ)⁻¹ := by
    simpa using congrArg (fun ψ : (ZMod N)ˣ →* ℂˣ => (ψ d : ℂ)) hχinv
  have hs : (χ d : ℂ) * (χ d : ℂ) = 1 := by
    calc
      (χ d : ℂ) * (χ d : ℂ) = (χ d : ℂ)⁻¹ * (χ d : ℂ) :=
        congrArg (fun x : ℂ => x * (χ d : ℂ)) hd
      _ = 1 := inv_mul_cancel₀ (χ d).ne_zero
  have hprod : ((χ d : ℂ) - 1) * ((χ d : ℂ) + 1) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linear_combination h)

/-- Every actual diamond translate of an integral single-character cusp form
has integral Fourier coefficients. No rationality of the character is assumed. -/
theorem diamond_integral_of_mem_character
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hχ : g ∈ cuspFormCharSpace k χ)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ))
    (d : (ZMod N)ˣ) :
    ∀ n : ℕ, ∃ z : ℤ,
      (qExpansion 1 (diamondOpCusp k d g)).coeff n = (z : ℂ) := by
  by_cases hg0 : g = 0
  · subst g
    simpa only [map_zero] using hg
  have hreal : HasRealQExpansion g := by
    intro n
    obtain ⟨z, hz⟩ := hg n
    exact ⟨(z : ℝ), by simpa using hz⟩
  intro n
  rw [diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ d hχ]
  rcases character_value_sign_of_real χ g hχ hg0 hreal d with hd | hd
  · rw [hd, one_smul]
    exact hg n
  · rw [hd, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_smul, smul_eq_mul]
    obtain ⟨z, hz⟩ := hg n
    refine ⟨-z, ?_⟩
    rw [hz]
    push_cast
    ring

/-- The actual good-prime Hecke operator preserves integrality on this
closed single-character case, at every nonzero level and every weight at least two. -/
theorem prime_hecke_integral_of_mem_character
    (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hχ : g ∈ cuspFormCharSpace k χ)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ n : ℕ, ∃ z : ℤ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n =
        (z : ℂ) := by
  have hcop : Nat.Coprime p N := (hp.coprime_iff_not_dvd).mpr hgood
  intro n
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g n]
  obtain ⟨z₁, hz₁⟩ := hg (p * n)
  rw [hz₁]
  split_ifs with hpn
  · rw [diamondOpCuspNat_of_coprime k hcop]
    obtain ⟨z₂, hz₂⟩ := diamond_integral_of_mem_character χ g hχ hg
      (ZMod.unitOfCoprime p hcop) (n / p)
    rw [hz₂]
    have he : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    refine ⟨z₁ + (p : ℤ) ^ (k - 1).toNat * z₂, ?_⟩
    rw [← he, zpow_natCast]
    push_cast
    rfl
  · exact ⟨z₁, by simp⟩

/-- The original rational-output conclusion, restricted only to actual
single-character input forms. No unit residue class or rational basis is supplied. -/
theorem prime_hecke_rational_of_mem_character
    (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hχ : g ∈ cuspFormCharSpace k χ)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ n : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n =
        (q : ℂ) := by
  intro n
  obtain ⟨z, hz⟩ := prime_hecke_integral_of_mem_character χ p g hk hp hgood hχ hg n
  exact ⟨(z : ℚ), by simpa using hz⟩

end DirectHeckeCharacter
