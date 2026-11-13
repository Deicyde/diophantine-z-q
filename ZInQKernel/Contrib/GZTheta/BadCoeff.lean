import ZInQKernel.Contrib.GZTheta.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# gz-theta: the leaf from `CMForm32` and the bad-prime coefficients

Second route to `ZInQ.GZDecomp.HeckeThetaNewform`, through Tau Ceti's existence of the newform
attached to an eigenform (Diamond–Shurman Prop. 5.8.4, `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`).
The theta series `f_d = cmForm F d` of level `32 d²` (from `CMForm32`) is an eigenform away from
the level; so some newform `g` of level `M ∣ 32 d²` and trivial character has its eigenvalues
`heckeCoeff d p` at the primes `p ∤ 2d`. What is left is local at `p ∣ 2d`:

* `BadCoeffCM`: such a newform has `p ∣ M` and `a_p(g) = 0` at every `p ∣ 2d`.

Then multiplicativity and the Hecke recursions (both sides) give `aₙ(g) = heckeCoeff d n` for
all `n`.
-/

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-- **The bad-prime coefficients of the newform of `ψ_d`.** A newform `g` of trivial character
whose coefficients at the primes `p ∤ 2d` are `heckeCoeff d p` has level divisible by every
`p ∣ 2d`, with `a_p(g) = 0` there; that is, `p² ∣ level` (the local component of `ψ_d` at
`p ∣ 2d` is ramified; conductor `32 d²`: Miyake, *Modular forms*, Thm 4.8.2, with strong
multiplicity one, Miyake Thm 4.6.19; UNVERIFIED locators). Not proved here. -/
def BadCoeffCM : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∀ (M : ℕ) [NeZero M] (g : Newform M 2), g.χ = 1 →
      (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p) →
      ∀ p : ℕ, p.Prime → p ∣ 2 * d → p ∣ M ∧ coeff g p = 0

/-- `heckeCoeff d (p ^ k) = 0` for `p ∣ 2d`, `k ≥ 1`. -/
theorem heckeCoeff_pow_of_dvd_two_mul {d p : ℕ} (hd4 : d % 4 = 1) (hp : p.Prime)
    (h : p ∣ 2 * d) {k : ℕ} (hk : 1 ≤ k) : heckeCoeff d (p ^ k) = 0 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | hpd
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst this
    exact heckeCoeff_two_pow d hk
  · exact heckeCoeff_pow_of_dvd (odd_of_mod_four hd4) hp hpd hk

/-- **Coefficients of a newform determined by its good and bad prime coefficients.** -/
theorem coeff_eq_heckeCoeff_of_good_bad {d M : ℕ} [NeZero M] (hd4 : d % 4 = 1)
    (hsq : Squarefree d) (g : Newform M 2) (hχ : g.χ = 1)
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ 2 * d)
    (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ 2 * d → p ∣ M ∧ coeff g p = 0) :
    ∀ n : ℕ, coeff g n = heckeCoeff d n := by
  obtain ⟨hmul, hpow⟩ :=
    (Eigenform.exists_toCuspForm_eq_and_χ_eq_iff_qExpansion_coeff_mul_and_prime_pow_add_two
      g.mem_charSpace g.isNorm).mp ⟨g.toEigenform, g.toEigenform_toCuspForm, g.toEigenform_χ⟩
  have hpp : ∀ p : ℕ, p.Prime → ∀ k : ℕ, coeff g (p ^ k) = heckeCoeff d (p ^ k) := by
    intro p hp
    have h1 : coeff g p = heckeCoeff d p := by
      by_cases h : p ∣ 2 * d
      · rw [(hbad p hp h).2, ← pow_one p, heckeCoeff_pow_of_dvd_two_mul hd4 hp h le_rfl]
      · exact hgood p hp h
    have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) p * (p : ℂ) ^ ((2 : ℤ) - 1) =
        if p ∣ 2 * d then 0 else (p : ℂ) := by
      by_cases h : p ∣ 2 * d
      · rw [ite_eq_left h, MulChar.map_nonunit _ (by
          rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp, not_not]
          exact (hbad p hp h).1), zero_mul]
      · have hc : Nat.Coprime p M := by
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          exact fun hpM => h (hM p hp hpM)
        rw [ite_eq_right h, ← ZMod.coe_unitOfCoprime p hc, MulChar.ofUnitHom_coe, hχ]
        simp
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k, ih with
      | 0, _ =>
        simp only [pow_zero]
        rw [heckeCoeff_one]
        exact g.isNorm
      | 1, _ => simpa using h1
      | r + 2, ih =>
        have e := hpow p hp r
        rw [hχp] at e
        change coeff g (p ^ (r + 2)) = coeff g p * coeff g (p ^ (r + 1)) -
          (if p ∣ 2 * d then 0 else (p : ℂ)) * coeff g (p ^ r) at e
        rw [e, heckePrimePow' hd4 hsq p hp r, h1, ih (r + 1) (by omega), ih r (by omega)]
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => exact hpp p hp k
  | zero =>
    rw [heckeCoeff_zero]
    exact CuspFormClass.qExpansion_coeff_zero _ one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map M)
  | one =>
    rw [heckeCoeff_one]
    exact g.isNorm
  | coprime a b _ _ hab ha hb =>
    have := hmul a b hab
    change coeff g (a * b) = coeff g a * coeff g b at this
    rw [this, ha, hb, heckeMult d a b hab]

/-- **`HeckeThetaNewform` from modularity of the level-32 form and the bad-prime
coefficients.** -/
theorem heckeThetaNewform_of_cmForm32_badCoeffCM (h32 : CMForm32) (hbad : BadCoeffCM) :
    HeckeThetaNewform := by
  intro d hd4 hsq
  have : NeZero d := ⟨by omega⟩
  obtain ⟨F, hF⟩ := h32
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway_cmForm hF d hd4 hsq
  obtain ⟨M, hM0, hMN, g, hgχ, hgev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      E.mem_charSpace E.ne_zero (a := fun p hp hpN => E.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun p hp hpN => E.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  have hg1 : g.χ = 1 := by
    rw [hEχ] at hgχ
    ext u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hMN u
    have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hgχ
    simpa using this
  have hE1 : (qExpansion 1 E.toCuspForm).coeff 1 = 1 := by
    rw [hE, qExpansion_cmForm_coeff hF d 1, heckeCoeff_one]
  have hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p := by
    intro p hp h
    have hpN : Nat.Coprime p (32 * d ^ 2) := by
      by_contra hc
      exact h ((dvd_two_mul_iff_not_coprime hp).mpr hc)
    have e1 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN)
    have e2 := E.qExpansion_coeff_eq_eigenvalue hE1 ⟨p, hp.pos⟩ hpN
    rw [hE, qExpansion_cmForm_coeff hF d] at e2
    change coeff g p = _ at e1
    rw [e1, hgev p hp hpN]
    exact e2.symm
  have hM : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ 2 * d := fun p hp hpM =>
    (dvd_two_mul_iff_not_coprime hp).mpr fun hc =>
      (Nat.Prime.coprime_iff_not_dvd hp).mp hc (hpM.trans hMN)
  exact ⟨M, hM0, g, hg1, fun n _ => coeff_eq_heckeCoeff_of_good_bad hd4 hsq g hg1 hM hgood
    (hbad d hd4 hsq M g hg1 hgood) n⟩

end ZInQ.GZTheta
