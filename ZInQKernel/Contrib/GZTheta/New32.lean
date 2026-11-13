import ZInQKernel.Contrib.GZTheta.Split
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Vanishing

/-!
# gz-theta: `η(4τ)²η(8τ)²` is new at level 32

The associated newform `g` of `f₁ = η(4τ)²η(8τ)²` (Tau Ceti, Diamond–Shurman 5.8.4) has level
`M ∣ 32`. If `M = 32` then `f₁ = g` (Diamond–Shurman 5.8.2) is new. Otherwise:
* `M = 1` is impossible (`S₂(SL₂(ℤ)) = 0`, Mathlib);
* for `M ∈ {2, 4, 8, 16}`, `f₁(τ) = g(τ) − a₂(g) g(2τ)` (the coefficients agree at odd `n`, and
  `a_{2n}(g) = a₂(g) a_n(g)`); applying the Fricke involution `τ ↦ −1/(32τ)`, under which
  `f₁(−1/(32τ)) = −32 τ² f₁(τ)` while `g(−1/(Mτ)) = c τ² g(τ)`, gives
  `−32 f₁(τ) = c (32/M)² g((32/M)τ) − a₂ c (16/M)² g((16/M)τ)`; dividing by `q` and letting
  `Im τ → ∞`, the left side tends to `−32` and the right side to `0` (for `M = 16`, `a₂(g) = 0`
  because `4 ∣ 16`: Tau Ceti, Miyake 4.6.17).
-/

open Complex Filter ModularForm UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### The Fricke involution on `f₁` -/

/-- `f₁(z) = η(4z)² η(8z)²` on `ℂ`. -/
def F₁ (z : ℂ) : ℂ := η (4 * z) ^ 2 * η (8 * z) ^ 2

theorem F₁_fricke {z : ℂ} (hz : 0 < z.im) : F₁ (-1 / (32 * z)) = -32 * z ^ 2 * F₁ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h8 : 0 < (8 * z).im := by simp; exact hz
  have h4 : 0 < (4 * z).im := by simp; exact hz
  unfold F₁
  rw [show 4 * (-1 / (32 * z)) = -1 / (8 * z) by field_simp; ring,
    show 8 * (-1 / (32 * z)) = -1 / (4 * z) by field_simp; ring,
    eta_sq_neg_inv h8, eta_sq_neg_inv h4]
  ring_nf
  rw [I_sq]
  ring

/-! ### The Fricke involution on a newform -/

theorem newform_fricke {M : ℕ} [NeZero M] (g : Newform M 2) (hχ : g.χ = 1) :
    ∃ c : ℂ, ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * g.toCuspForm ⟨z, hz⟩ := by
  have hfr := g.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  set ε := g.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer M 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine ⟨ε * M, fun z hz hz' => ?_⟩
  have h := congrArg (fun F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ M).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ M) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ M • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((M : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ M) (⟨z, hz⟩ : ℍ) = (M : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ M).det : ℝ)| = M := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = A at h ⊢
  generalize g.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((M : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h


/-! ### The coefficients of the associated newform -/

theorem heckeCoeff_one_even (m : ℕ) : heckeCoeff 1 (2 * m) = 0 := by
  rw [heckeCoeff_one_eq_sum_Soe]
  refine Finset.sum_eq_zero fun p hp => ?_
  exfalso
  simp only [Soe, Finset.mem_filter, mem_normFiber] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have : (p.1 ^ 2 + p.2 ^ 2) % 2 = 1 := by
    have e1 : p.1 ^ 2 % 2 = 1 := by
      rw [pow_two, Int.mul_emod, h2]; norm_num
    have e2 : p.2 ^ 2 % 2 = 0 := by
      rw [pow_two, Int.mul_emod, h3]; norm_num
    omega
  push_cast at h1
  omega

/-- The coefficient facts for a normalized trivial-character newform `g` of level `M ∣ 16`,
`2 ∣ M`, whose eigenvalues at the odd primes are `heckeCoeff 1 p`. -/
theorem coeff_newform_odd_even {M : ℕ} [NeZero M] (hM16 : M ∣ 16) (hM2 : 2 ∣ M)
    (g : Newform M 2) (hχ : g.χ = 1)
    (hgood : ∀ p : ℕ, p.Prime → p ≠ 2 → coeff g p = heckeCoeff 1 p) :
    (∀ n : ℕ, n % 2 = 1 → coeff g n = heckeCoeff 1 n) ∧
      ∀ n : ℕ, coeff g (2 * n) = coeff g 2 * coeff g n := by
  obtain ⟨hmul, hpow⟩ :=
    (Eigenform.exists_toCuspForm_eq_and_χ_eq_iff_qExpansion_coeff_mul_and_prime_pow_add_two
      g.mem_charSpace g.isNorm).mp ⟨g.toEigenform, g.toEigenform_toCuspForm, g.toEigenform_χ⟩
  have hcopM : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.Coprime p M := by
    intro p hp hp2
    have h16 : Nat.Coprime p 16 := by
      have : Nat.Coprime p (2 ^ 4) := Nat.Coprime.pow_right 4
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      simpa using this
    exact h16.coprime_dvd_right hM16
  have hχp : ∀ p : ℕ, (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) p =
      if Nat.Coprime p M then 1 else 0 := by
    intro p
    split_ifs with hc
    · rw [← ZMod.coe_unitOfCoprime p hc, MulChar.ofUnitHom_coe, hχ]; simp
    · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  -- odd prime powers
  have hpp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ k : ℕ, coeff g (p ^ k) = heckeCoeff 1 (p ^ k) := by
    intro p hp hp2
    have h1 := hgood p hp hp2
    have hp2' : ¬ p ∣ 2 * 1 := by
      rw [mul_one]; intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k, ih with
      | 0, _ => simp only [pow_zero]; rw [heckeCoeff_one]; exact g.isNorm
      | 1, _ => simpa using h1
      | r + 2, ih =>
        have e := hpow p hp r
        rw [hχp, if_pos (hcopM p hp hp2)] at e
        change coeff g (p ^ (r + 2)) = coeff g p * coeff g (p ^ (r + 1)) -
          1 * (p : ℂ) ^ ((2 : ℤ) - 1) * coeff g (p ^ r) at e
        rw [e, heckePrimePow' (by norm_num) squarefree_one p hp r, if_neg hp2', h1,
          ih (r + 1) (by omega), ih r (by omega)]
        norm_num
  refine ⟨fun n hn => ?_, fun n => ?_⟩
  · -- odd `n`
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        omega
      exact hpp p hp hp2 k
    | zero => omega
    | one => rw [heckeCoeff_one]; exact g.isNorm
    | coprime a b _ _ hab ha hb =>
      obtain ⟨ha', hb'⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr hn)
      have hao : a % 2 = 1 := Nat.odd_iff.mp ha'
      have hbo : b % 2 = 1 := Nat.odd_iff.mp hb'
      have := hmul a b hab
      change coeff g (a * b) = coeff g a * coeff g b at this
      rw [this, ha hao, hb hbo, heckeMult 1 a b hab]
  · -- `a_{2n} = a₂ a_n`
    have hχ2 : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) ((2 : ℕ) : ZMod M) = 0 := by
      have h := hχp 2
      rw [if_neg] at h
      · exact h
      · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
        exact not_not.mpr hM2
    have h2pow : ∀ j : ℕ, coeff g (2 ^ j) = coeff g 2 ^ j := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        match j, ih with
        | 0, _ => simp only [pow_zero]; exact g.isNorm
        | 1, _ => simp
        | r + 2, ih =>
          have e := hpow 2 Nat.prime_two r
          rw [hχ2, zero_mul, zero_mul, sub_zero] at e
          change coeff g (2 ^ (r + 2)) = coeff g 2 * coeff g (2 ^ (r + 1)) at e
          rw [e, ih (r + 1) (by omega), pow_succ' (coeff g 2) (r + 1)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [mul_zero]
      have h0 : coeff g 0 = 0 := CuspFormClass.qExpansion_coeff_zero _ one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map M)
      rw [h0, mul_zero]
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hcop : ∀ j, Nat.Coprime (2 ^ j) m := fun j =>
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    have e1 := hmul (2 ^ (k + 1)) m (hcop (k + 1))
    have e2 := hmul (2 ^ k) m (hcop k)
    change coeff g (2 ^ (k + 1) * m) = coeff g (2 ^ (k + 1)) * coeff g m at e1
    change coeff g (2 ^ k * m) = coeff g (2 ^ k) * coeff g m at e2
    rw [show 2 * (2 ^ k * m) = 2 ^ (k + 1) * m by ring, e1, e2, h2pow, h2pow, pow_succ']
    ring

end ZInQ.GZTheta
