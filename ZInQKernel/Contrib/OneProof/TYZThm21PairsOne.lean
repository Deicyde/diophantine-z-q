import ZInQKernel.Contrib.OneProof.TYZThm11Genus
import ZInQKernel.Contrib.OneProof.TYZGenusFold.QI

/-!
# Variant C (task tyz-genus): TYZ Theorem 2.1 including `n = 1` gives `h11` and `hL29` (one leaf for two)

`TYZThm21PairsC1` is `TYZThm21PairsC` for every squarefree `n ≥ 1` (not only `n > 1`) in the odd classes, with the
displayed formula written `2^a P = ±2^k w_K 𝓛(d₁)𝓛(d₂)` (`a = 1`; for `n > 1` this is `P = ±2^{k−1} w_K 𝓛𝓛`, and at
`n = 1`, `k = 0`, it reads `P(1, 1) = ±𝓛(1)²` with `w_{ℚ(i)} = 2`). Whether TYZ's Theorem 2.1 covers `n = 1` was not
checked against the print (the source was not on the host): **pending reading**.

* `tyzThm21PairsC_of_C1`: it implies `TYZThm21PairsC`;
* `tyzLcalOne_of_C1`: its instance `n = 1` gives `𝓛(1)² = 1` (`TYZLcalOne`): `P(1, 1) = f_1(1) = ±F(1)` is odd
  (`Cl(ℚ(i)) = 1`, hfx-proof/hp23-proof's generator), so `𝓛(1)²` is an odd integer, and t21-proof's rigorous bounds
  on `L(C₁, 1)` (`Re ≥ 0.09`, `‖·‖ ≤ 1.26`, `∫₁^∞ dx/√(x³−x) ≥ 2`) leave only `1`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open scoped Quaternion
open IsDedekindDomain

/-- **TYZ Theorem 2.1 (L554–559) for every decomposition, odd classes, every squarefree `n ≥ 1`, complex sign
choices.** As `TYZThm21PairsC` with `n = 1` allowed and the formula multiplied by `2^a = 2`. -/
def TYZThm21PairsC1 : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          2 * (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ n.primeFactors.card *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem tyzThm21PairsC_of_C1 (h : TYZThm21PairsC1) : TYZThm21PairsC := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  obtain ⟨hA, hB⟩ := h n hsq hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  refine ⟨hA, fun h8 => ?_⟩
  obtain ⟨ε, hε, heq⟩ := hB h8
  refine ⟨ε, hε, ?_⟩
  have hk : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h1)
  have h2k : (2 : ℂ) ^ n.primeFactors.card = 2 * 2 ^ (n.primeFactors.card - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2k] at heq
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0)
  linear_combination heq

theorem twoRep_zero (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) : twoRep v (0, 0, 0) = 1 := by
  have h : twoRepQ (0, 0, 0) = 1 := by ext <;> simp [twoRepQ]
  rw [twoRep, h, ιAt, map_one, mul_one, ← map_add, add_sub_cancel, map_one]

/-- **`𝓛(1)² = 1` from TYZ Theorem 2.1 at `n = 1`.** -/
theorem tyzLcalOne_of_C1 (h : TYZThm21PairsC1) : TYZLcalOne := by
  have hτe := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of
    ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
    ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof)
  obtain ⟨τ, hτ⟩ := hτe 1 squarefree_one (Or.inl rfl)
  obtain ⟨v, hv, F, hP, hodd, -⟩ := ZInQ.Contrib.HP23Proof.partition_one8 squarefree_one rfl hτ
  obtain ⟨f, hf, -⟩ := ZInQ.Contrib.HfxProof.testVector_of_partition hv F hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2
  obtain ⟨s, hs, hfs⟩ := ZInQ.Contrib.HP23Proof.tv_eq_sign hv hP hf
  let ℓ : ℕ → ℂ := fun m => lcalSq m ^ ((2 : ℕ)⁻¹ : ℂ)
  have hℓ : IsLcalSignC ℓ := fun m _ _ => Complex.cpow_nat_inv_pow _ two_ne_zero
  obtain ⟨-, hB⟩ := h 1 squarefree_one (Or.inl rfl) τ hτ f hf ℓ hℓ 1 1 rfl
  obtain ⟨ε, hε, heq⟩ := hB rfl
  have hq : quadPeriod 1 τ f 1 = f 1 := by
    rw [quadPeriod_one]
    have := classGroup_one_subsingleton
    rw [Fintype.sum_subsingleton _ 1]
    have h1 : FiniteAdeleRing.toClassGroup (𝓞 (QNeg 1)) (QNeg 1) (clLift 1 1) =
        FiniteAdeleRing.toClassGroup (𝓞 (QNeg 1)) (QNeg 1) 1 := Subsingleton.elim _ _
    rw [tv_eq_of_toClassGroup_eq hf.1 h1, map_one, Units.val_one]
  have hf1 : f 1 = s * F (0, 0, 0) :=
    hfs 1 (0, 0, 0) (by rw [Units.val_one, ← twoRep_zero v]; exact ZInQ.Contrib.HfxProof.mem_DC_self _)
  have hp : (1 : ℕ).primeFactors.card = 0 := by simp
  rw [hq, hf1, hp, torsionOrder_one] at heq
  -- `𝓛(1)² = N`, `N = ε s F(1)` an odd integer
  have hsq1 : lcalSq 1 = ((ε * s * F (0, 0, 0) : ℤ) : ℂ) := by
    have hεsq : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [← hℓ 1 squarefree_one (Or.inl rfl)]
    push_cast at heq ⊢
    linear_combination (-(ε : ℂ) / 2) * heq + (-(ℓ 1 ^ 2)) * hεsq
  set N : ℤ := ε * s * F (0, 0, 0) with hN
  have hNodd : Odd N := by
    have hF := hodd (0, 0, 0) rfl
    rcases hε with rfl | rfl <;> rcases hs with rfl | rfl <;> simp [hN, hF]
  obtain ⟨hre, hle⟩ := ZInQ.Contrib.T21Proof.lValOne_one_bounds
  have hω := ZInQ.Contrib.TYZLcal.omegaInt_ge_two
  have hL : lValOne 1 = (N : ℂ) * ((omegaInt : ℂ) / 4) := by
    have e := ZInQ.Contrib.TYZLcal.lcalSq_one
    rw [hsq1] at e
    have hΩ : ((omegaInt : ℂ) / 4) ≠ 0 := by
      have : (omegaInt : ℂ) ≠ 0 := by exact_mod_cast (show omegaInt ≠ 0 by linarith)
      exact div_ne_zero this (by norm_num)
    rw [e, div_mul_cancel₀ _ hΩ]
  have hre' : 0.09 ≤ (N : ℝ) * (omegaInt / 4) := by
    have := hre
    rw [hL] at this
    simpa [Complex.mul_re, Complex.div_re] using this
  have hle' : |(N : ℝ)| * (omegaInt / 4) ≤ 1.26 := by
    have := hle
    rw [hL, norm_mul, norm_div, Complex.norm_real, Complex.norm_intCast,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ omegaInt)] at this
    norm_num at this ⊢
    linarith
  have hNpos : 0 < (N : ℝ) := by
    by_contra hc
    push Not at hc
    have : (N : ℝ) * (omegaInt / 4) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hNle : (N : ℝ) < 3 := by
    rw [abs_of_pos hNpos] at hle'
    nlinarith [mul_le_mul_of_nonneg_left hω hNpos.le]
  have hN1 : N = 1 := by
    have h1 : 0 < N := by exact_mod_cast hNpos
    have h2 : N < 3 := by exact_mod_cast hNle
    obtain ⟨k, hk⟩ := hNodd
    omega
  unfold TYZLcalOne
  rw [hsq1, hN1]
  simp

/-- **`h11` from TYZ Theorem 2.1 including `n = 1`.** -/
theorem tyzThm11Integral_of_C1 (h : TYZThm21PairsC1) : TYZThm11Integral :=
  tyzThm11Integral_of_thm21C (tyzThm21PairsC_of_C1 h) (tyzLcalOne_of_C1 h)

/-- **`hL29` from TYZ Theorem 2.1 including `n = 1`.** -/
theorem tyzLemma29PrintedNe3_of_C1 (h : TYZThm21PairsC1) : TYZLemma29PrintedNe3 :=
  tyzLemma29PrintedNe3_of_thm21C (tyzThm21PairsC_of_C1 h)

end ZInQ.Contrib.TYZGenusFold
