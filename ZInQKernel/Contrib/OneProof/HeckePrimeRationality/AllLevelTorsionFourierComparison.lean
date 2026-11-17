import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionFourierKernel
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaWeierstrass
import Mathlib.Algebra.Ring.GeomSum

/-!
# Global comparison for the actual torsion Kronecker kernels

The comparison is formed from the intrinsic theta quotient and an actual
logarithmic derivative. Its candidate singularities are removed by a common
entire numerator and actual divided differences, never by a Fourier premise.
-/

noncomputable section

open Complex UpperHalfPlane Filter Function
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionFourierComparison

open CompletedTheta TorsionFourierKernel
open QuasiThetaMultiplicationTwo (regularizedQuotient)

variable (N : ℕ) [NeZero N]

/-- The finite torsion pairing with the tau-first row convention. -/
def character (a b r s : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((b : ℂ) * r - (a : ℂ) * s) / (N : ℂ))

lemma finite_geometric (x : ℂ) (hx : x ^ N = 1) :
    (∑ j : Fin N, x ^ (j : ℕ)) = if x = 1 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst x
    simp
  · rw [Fin.sum_univ_eq_sum_range]
    have hs := mul_neg_geom_sum x N
    rw [hx, sub_self] at hs
    exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr (Ne.symm h))

lemma w_pow_level (r : ℤ) : Torsion.w N r ^ N = 1 := by
  have hz : Torsion.zeta N ^ N = 1 := (AllLevelTorsionCoefficients.complex_root_primitive N).pow_eq_one
  rw [Torsion.w, ← zpow_natCast, ← zpow_mul, mul_comm r (N : ℤ), zpow_mul,
    zpow_natCast, hz, one_zpow]

lemma character_factor (a b : ℕ) (r s : ℤ) :
    character N a b r s = Torsion.w N (-s) ^ a * Torsion.w N r ^ b := by
  rw [AllLevelTorsionCoefficients.w_eq_exp, AllLevelTorsionCoefficients.w_eq_exp,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  dsimp [character]
  congr 1
  push_cast
  ring

/-- The finite pairing is orthogonal, at all positive levels including composite levels. -/
lemma character_sum (r s : ℤ) :
    (∑ a : Fin N, ∑ b : Fin N, character N (a : ℕ) (b : ℕ) r s) =
      if (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s then (N : ℂ) ^ 2 else 0 := by
  simp_rw [character_factor, ← Finset.mul_sum]
  rw [← Finset.sum_mul,
    finite_geometric N (Torsion.w N (-s)) (w_pow_level N (-s)),
    finite_geometric N (Torsion.w N r) (w_pow_level N r)]
  simp only [AllLevelTorsionCoefficients.w_eq_one_iff N (-s),
    AllLevelTorsionCoefficients.w_eq_one_iff N r, Int.dvd_neg]
  split_ifs <;> simp_all [sq]

lemma finite_good_iff (a b : Fin N) :
    ¬ ((N : ℤ) ∣ ((a : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((b : ℕ) : ℤ)) ↔ a ≠ 0 ∨ b ≠ 0 := by
  have ha : (N : ℤ) ∣ ((a : ℕ) : ℤ) ↔ a = 0 := by
    constructor
    · intro h
      have := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast h) a.isLt
      exact Fin.ext this
    · intro h; subst a; simp
  have hb : (N : ℤ) ∣ ((b : ℕ) : ℤ) ↔ b = 0 := by
    constructor
    · intro h
      have := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast h) b.isLt
      exact Fin.ext this
    · intro h; subst b; simp
  rw [ha, hb]
  tauto

lemma character_sum_nonzero (r s : ℤ) :
    (∑ a : Fin N, ∑ b : Fin N,
      if a = 0 ∧ b = 0 then 0 else character N (a : ℕ) (b : ℕ) r s) =
      (if (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s then (N : ℂ) ^ 2 else 0) - 1 := by
  classical
  have he : ∀ a b : Fin N,
      (if a = 0 ∧ b = 0 then 0 else character N (a : ℕ) (b : ℕ) r s) =
        character N (a : ℕ) (b : ℕ) r s - if a = 0 ∧ b = 0 then 1 else 0 := by
    intro a b
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp [character]
    · simp
  simp_rw [he, Finset.sum_sub_distrib]
  rw [character_sum N]
  congr 1
  simp [ite_and]

lemma kernel_period_one (a b : ℤ) (τ : ℍ) : Periodic (kernel N a b τ) (1 : ℂ) := by
  intro z
  have h := kernel_add_nat_one_div N a b τ z N
  have hp : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [show (N : ℂ) * (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) =
        (-a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp]
    simpa using Complex.exp_int_mul_two_pi_mul_I (-a)
  rw [hp] at h
  simpa [Nat.cast_ne_zero.mpr (NeZero.ne N)] using h

lemma kernel_period_tau (a b : ℤ) (τ : ℍ) : Periodic (kernel N a b τ) (τ : ℂ) := by
  intro z
  have h := kernel_add_nat_tau_div N a b τ z N
  have hp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (N : ℂ)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [show (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (N : ℂ)) =
        (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I b
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simpa [hp, hN, mul_div_cancel_left₀] using h

/-- The dilated actual theta. -/
def dilated (τ : ℍ) (z : ℂ) : ℂ := H τ ((N : ℂ) * z)

lemma differentiable_dilated (τ : ℍ) : Differentiable ℂ (dilated N τ) :=
  (differentiable_H τ).comp (by fun_prop)

lemma deriv_dilated (τ : ℍ) (z : ℂ) :
    deriv (dilated N τ) z = Hder τ ((N : ℂ) * z) * (N : ℂ) := by
  have hm : HasDerivAt (fun w : ℂ => (N : ℂ) * w) (N : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (N : ℂ)
  exact (hasDerivAt_H τ ((N : ℂ) * z) |>.comp z hm).deriv

lemma dilated_zero_of_H_zero (τ : ℍ) (z : ℂ) (hz : H τ z = 0) : dilated N τ z = 0 := by
  obtain ⟨m, n, he⟩ := (CompletedTheta.H_zero_iff_lattice τ z).mp hz
  apply (CompletedTheta.H_zero_iff_lattice τ _).mpr
  refine ⟨(N : ℤ) * m, (N : ℤ) * n, ?_⟩
  push_cast
  rw [he]
  ring

lemma deriv_dilated_ne (τ : ℍ) (z : ℂ) (hz : dilated N τ z = 0) :
    deriv (dilated N τ) z ≠ 0 := by
  rw [deriv_dilated]
  apply mul_ne_zero
  · rw [← deriv_H]
    apply ThetaWeierstrass.deriv_H_ne_zero_of_mem τ
    exact (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mp hz
  · exact Nat.cast_ne_zero.mpr (NeZero.ne N)

/-- An entire actual theta quotient, with derivative-defined values at simple zeros. -/
def dilationQuotient (τ : ℍ) : ℂ → ℂ := regularizedQuotient (dilated N τ) (H τ)

lemma differentiable_dilationQuotient (τ : ℍ) : Differentiable ℂ (dilationQuotient N τ) := by
  apply QuasiThetaMultiplicationTwo.differentiable_regularizedQuotient
    (differentiable_dilated N τ) (differentiable_H τ)
  intro c hc
  exact ⟨dilated_zero_of_H_zero N τ c hc, ThetaWeierstrass.deriv_H_ne_zero_of_mem τ
    ((ThetaWeierstrass.H_zero_iff_mem_lattice τ c).mp hc)⟩

/-- The actual entire numerator of one normalized Kronecker kernel. -/
def kernelNumerator (a b : ℤ) (τ : ℍ) (z : ℂ) : ℂ :=
  Hder τ 0 / H τ (-(torsionPoint N a b τ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) *
      H τ ((N : ℂ) * z - torsionPoint N a b τ)

lemma differentiable_kernelNumerator (a b : ℤ) (τ : ℍ) :
    Differentiable ℂ (kernelNumerator N a b τ) := by
  unfold kernelNumerator
  apply Differentiable.mul
  · fun_prop
  · exact (differentiable_H τ).comp (by fun_prop)

lemma kernel_eq_quotient (a b : ℤ) (τ : ℍ) (z : ℂ) :
    kernel N a b τ z = kernelNumerator N a b τ z / dilated N τ z := by
  dsimp [kernel, kernelNumerator, dilated]
  ring

/-- A common entire numerator for the Fourier comparison. -/
def comparisonNumerator (τ : ℍ) (z : ℂ) : ℂ :=
  -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N, kernelNumerator N (a : ℕ) (b : ℕ) τ z) -
    (N : ℂ) * Hder τ ((N : ℂ) * z) +
      (N : ℂ) ^ 2 * Hder τ z * dilationQuotient N τ z

/-- The raw off-pole comparison. -/
def rawComparison (τ : ℍ) (z : ℂ) : ℂ :=
  -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N, kernel N (a : ℕ) (b : ℕ) τ z) -
    (N : ℂ) * (Hder τ ((N : ℂ) * z) / H τ ((N : ℂ) * z)) +
      (N : ℂ) ^ 2 * (Hder τ z / H τ z)

lemma rawComparison_as_logs (τ : ℍ) (z : ℂ) : rawComparison N τ z =
    -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N, kernel N (a : ℕ) (b : ℕ) τ z) -
      (N : ℂ) * ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) * z) +
        (N : ℂ) ^ 2 * ThetaWeierstrass.logDerivative (H τ) z := by
  dsimp [rawComparison, ThetaWeierstrass.logDerivative]
  rw [deriv_H, deriv_H]

/-- The common numerator is entire before any pole is removed. -/
lemma differentiable_comparisonNumerator (τ : ℍ) : Differentiable ℂ (comparisonNumerator N τ) := by
  have hder : Differentiable ℂ (Hder τ) := fun z => (Hder_analytic τ z).differentiableAt
  unfold comparisonNumerator
  apply Differentiable.add
  · apply Differentiable.sub
    · apply Differentiable.const_mul
      apply Differentiable.fun_sum
      intro a _
      apply Differentiable.fun_sum
      intro b _
      exact differentiable_kernelNumerator N (a : ℕ) (b : ℕ) τ
    · apply Differentiable.const_mul
      exact hder.comp (by fun_prop)
  · exact (hder.const_mul ((N : ℂ) ^ 2)).mul (differentiable_dilationQuotient N τ)

lemma rawComparison_eq_quotient (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    rawComparison N τ z = comparisonNumerator N τ z / dilated N τ z := by
  have hHz : H τ z ≠ 0 := fun h => hz (dilated_zero_of_H_zero N τ z h)
  have hV : dilationQuotient N τ z = dilated N τ z / H τ z := by
    simp [dilationQuotient, regularizedQuotient, hHz]
  have hsum : (∑ a : Fin N, ∑ b : Fin N, kernel N (a : ℕ) (b : ℕ) τ z) =
      (∑ a : Fin N, ∑ b : Fin N, kernelNumerator N (a : ℕ) (b : ℕ) τ z) / dilated N τ z := by
    simp_rw [kernel_eq_quotient, Finset.sum_div]
  rw [rawComparison, comparisonNumerator, hsum, hV]
  change _ - _ * (Hder τ ((N : ℂ) * z) / dilated N τ z) + _ = _
  field_simp [hz, hHz]

/-- A simple analytic denominator gives its actual residue by the derivative slope. -/
lemma simple_quotient_residue {F G : ℂ → ℂ} {c : ℂ}
    (hF : ContinuousAt F c) (hG : DifferentiableAt ℂ G c) (hz : G c = 0)
    (hd : deriv G c ≠ 0) :
    Tendsto (fun z : ℂ => z * (F (c + z) / G (c + z))) (𝓝[≠] 0) (𝓝 (F c / deriv G c)) := by
  have hs : Tendsto (fun z : ℂ => G (c + z) / z) (𝓝[≠] 0) (𝓝 (deriv G c)) := by
    simpa [smul_eq_mul, hz, div_eq_mul_inv, mul_comm] using hG.hasDerivAt.tendsto_slope_zero
  have hnum : Tendsto (fun z : ℂ => F (c + z)) (𝓝[≠] 0) (𝓝 (F c)) := by
    have hc : ContinuousAt F (c + (0 : ℂ)) := by simpa using hF
    have ht := hc.comp (by fun_prop : ContinuousAt (fun z : ℂ => c + z) 0)
    simpa only [Function.comp_def, add_zero] using ht.tendsto.mono_left nhdsWithin_le_nhds
  convert hnum.mul (hs.inv₀ hd) using 1
  · ext z
    simp only [inv_div]
    ring
  · rw [div_eq_mul_inv]

/-- The logarithmic derivative has residue one at a simple zero, zero elsewhere. -/
lemma log_residue {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ)
    (hd : F c = 0 → deriv F c ≠ 0) :
    Tendsto (fun z : ℂ => z * ThetaWeierstrass.logDerivative F (c + z)) (𝓝[≠] 0)
      (𝓝 (if F c = 0 then (1 : ℂ) else 0)) := by
  classical
  by_cases hz : F c = 0
  · rw [if_pos hz]
    simpa [ThetaWeierstrass.logDerivative, div_self (hd hz)] using
      simple_quotient_residue (hF.analyticAt c).deriv.continuousAt (hF c) hz (hd hz)
  · rw [if_neg hz]
    have hc := (ThetaWeierstrass.analyticAt_logDerivative hF hz).continuousAt
    have ht : Tendsto (fun z : ℂ => ThetaWeierstrass.logDerivative F (c + z)) (𝓝[≠] 0)
        (𝓝 (ThetaWeierstrass.logDerivative F c)) := by
      have hc' : ContinuousAt (ThetaWeierstrass.logDerivative F) (c + (0 : ℂ)) := by simpa using hc
      have hct := hc'.comp (by fun_prop : ContinuousAt (fun z : ℂ => c + z) 0)
      simpa only [Function.comp_def, add_zero] using hct.tendsto.mono_left nhdsWithin_le_nhds
    have h0 : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h0.mul ht

/-- The logarithmic expression has the correct residue at every candidate pole. -/
lemma logarithmic_comparison_residue (τ : ℍ) (c : ℂ) (hc : dilated N τ c = 0) :
    Tendsto (fun z : ℂ => z * ((N : ℂ) * (Hder τ ((N : ℂ) * (c + z)) /
      H τ ((N : ℂ) * (c + z))) - (N : ℂ) ^ 2 * (Hder τ (c + z) / H τ (c + z))))
      (𝓝[≠] 0) (𝓝 (1 - (N : ℂ) ^ 2 * if H τ c = 0 then 1 else 0)) := by
  have hd := log_residue (differentiable_dilated N τ) c (deriv_dilated_ne N τ c)
  rw [if_pos hc] at hd
  have hh := log_residue (differentiable_H τ) c (fun h =>
    ThetaWeierstrass.deriv_H_ne_zero_of_mem τ ((ThetaWeierstrass.H_zero_iff_mem_lattice τ c).mp h))
  have he : ∀ w : ℂ, ThetaWeierstrass.logDerivative (dilated N τ) w =
      (N : ℂ) * (Hder τ ((N : ℂ) * w) / H τ ((N : ℂ) * w)) := by
    intro w
    change deriv (dilated N τ) w / dilated N τ w = _
    rw [deriv_dilated]
    dsimp [dilated]
    ring
  convert hd.sub (hh.const_mul ((N : ℂ) ^ 2)) using 1
  · ext z
    rw [he]
    dsimp [ThetaWeierstrass.logDerivative]
    rw [deriv_H]
    ring

/-- Every dilated zero has a finite torsion representative plus an actual lattice translate. -/
lemma pole_representative (τ : ℍ) (c : ℂ) (hc : dilated N τ c = 0) :
    ∃ r s : Fin N, ∃ m n : ℤ,
      c = torsionPoint N (r : ℕ) (s : ℕ) τ + (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
  obtain ⟨m, n, hNc⟩ := (CompletedTheta.H_zero_iff_lattice τ ((N : ℂ) * c)).mp hc
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNz : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  let r : Fin N := ⟨(n % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg n hN0
    have h1 := Int.emod_lt_of_pos n hNz
    omega⟩
  let s : Fin N := ⟨(m % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg m hN0
    have h1 := Int.emod_lt_of_pos m hNz
    omega⟩
  have hr : ((r : ℕ) : ℤ) = n % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg n hN0)
  have hs : ((s : ℕ) : ℤ) = m % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg m hN0)
  have hn : (n : ℂ) = ((r : ℕ) : ℂ) + (N : ℂ) * ((n / (N : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast (show n = ((r : ℕ) : ℤ) + (N : ℤ) * (n / (N : ℤ)) by
      rw [hr]; exact (Int.emod_add_mul_ediv n (N : ℤ)).symm)
  have hm : (m : ℂ) = ((s : ℕ) : ℂ) + (N : ℂ) * ((m / (N : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast (show m = ((s : ℕ) : ℤ) + (N : ℤ) * (m / (N : ℤ)) by
      rw [hs]; exact (Int.emod_add_mul_ediv m (N : ℤ)).symm)
  refine ⟨r, s, m / (N : ℤ), n / (N : ℤ), ?_⟩
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  dsimp [torsionPoint]
  push_cast
  field_simp [hN]
  rw [hm, hn] at hNc
  linear_combination hNc

lemma kernel_lattice_translate (a b : ℤ) (τ : ℍ) (z : ℂ) (m n : ℤ) :
    kernel N a b τ (z + (m : ℂ) + (n : ℂ) * (τ : ℂ)) = kernel N a b τ z := by
  have h1 := (kernel_period_one N a b τ).int_mul m z
  have ht := (kernel_period_tau N a b τ).int_mul n (z + (m : ℂ))
  simp only [mul_one] at h1
  exact ht.trans h1

lemma H_zero_representative (τ : ℍ) (c : ℂ) (r s : Fin N) (m n : ℤ)
    (he : c = torsionPoint N (r : ℕ) (s : ℕ) τ + (m : ℂ) + (n : ℂ) * (τ : ℂ)) :
    H τ c = 0 ↔ r = 0 ∧ s = 0 := by
  have hshift : (m : ℂ) + (n : ℂ) * (τ : ℂ) ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    exact (ThetaWeierstrass.mem_periodPair_lattice_iff τ _).mpr ⟨m, n, rfl⟩
  have hL : c ∈ (ThetaWeierstrass.periodPair τ).lattice ↔
      torsionPoint N (r : ℕ) (s : ℕ) τ ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    rw [he, add_assoc]
    constructor
    · intro h
      simpa using (ThetaWeierstrass.periodPair τ).lattice.sub_mem h hshift
    · intro h
      exact (ThetaWeierstrass.periodPair τ).lattice.add_mem h hshift
  rw [ThetaWeierstrass.H_zero_iff_mem_lattice, hL, ← ThetaWeierstrass.H_zero_iff_mem_lattice]
  constructor
  · intro h
    by_contra hb
    have hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ)) := by
      rw [finite_good_iff N r s]
      tauto
    exact H_torsion_ne_zero N (NeZero.pos N) τ (r : ℕ) (s : ℕ) hg h
  · rintro ⟨rfl, rfl⟩
    simpa [torsionPoint] using H_zero τ

lemma kernel_residue_at_pole (a b : Fin N) (τ : ℍ) (c : ℂ) (r s : Fin N) (m n : ℤ)
    (he : c = torsionPoint N (r : ℕ) (s : ℕ) τ + (m : ℂ) + (n : ℂ) * (τ : ℂ)) :
    Tendsto (fun z : ℂ => z * kernel N (a : ℕ) (b : ℕ) τ (c + z)) (𝓝[≠] 0)
      (𝓝 (if a = 0 ∧ b = 0 then 0 else character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) / (N : ℂ))) := by
  classical
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    simpa [kernel_zero_row] using (tendsto_const_nhds :
      Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝[≠] 0) (𝓝 0))
  · rw [ite_eq_right hab]
    have hg := (finite_good_iff N a b).mpr (by tauto)
    have htr : ∀ z : ℂ, kernel N (a : ℕ) (b : ℕ) τ (c + z) =
        kernel N (a : ℕ) (b : ℕ) τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ) := by
      intro z
      rw [he, show (torsionPoint N (r : ℕ) (s : ℕ) τ + (m : ℂ) + (n : ℂ) * (τ : ℂ)) + z =
        (z + torsionPoint N (r : ℕ) (s : ℕ) τ) + (m : ℂ) + (n : ℂ) * (τ : ℂ) by ring,
        kernel_lattice_translate]
    simp_rw [htr]
    simpa [character, Int.cast_natCast] using kernel_residue_torsion N (a : ℕ) (b : ℕ) τ hg r s

/-- The finite kernel sum has exactly the residues needed at every actual dilated zero. -/
lemma kernel_sum_residue (τ : ℍ) (c : ℂ) (hc : dilated N τ c = 0) :
    Tendsto (fun z : ℂ => z * (∑ a : Fin N, ∑ b : Fin N, kernel N (a : ℕ) (b : ℕ) τ (c + z)))
      (𝓝[≠] 0) (𝓝 (((if H τ c = 0 then (N : ℂ) ^ 2 else 0) - 1) / (N : ℂ))) := by
  classical
  obtain ⟨r, s, m, n, he⟩ := pole_representative N τ c hc
  have ht := tendsto_finset_sum (Finset.univ : Finset (Fin N)) (fun a _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin N)) (fun b _ =>
      kernel_residue_at_pole N a b τ c r s m n he))
  have hv : (∑ a : Fin N, ∑ b : Fin N,
      if a = 0 ∧ b = 0 then (0 : ℂ) else character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) / (N : ℂ)) =
      ((if H τ c = 0 then (N : ℂ) ^ 2 else 0) - 1) / (N : ℂ) := by
    have hterm : ∀ a b : Fin N, (if a = 0 ∧ b = 0 then (0 : ℂ) else
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) / (N : ℂ)) =
        (if a = 0 ∧ b = 0 then 0 else character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) / (N : ℂ) := by
      intro a b
      by_cases hab : a = 0 ∧ b = 0
      · simp [hab]
      · simp only [ite_eq_right hab]
    have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin N))) rfl (fun a _ =>
      Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin N))) rfl (fun b _ => hterm a b))
    rw [hsum]
    simp_rw [← Finset.sum_div]
    rw [character_sum_nonzero]
    have hd : (N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ) ↔ r = 0 ∧ s = 0 := by
      have h := not_congr (finite_good_iff N r s)
      simpa only [not_not, not_or] using h
    simp only [hd, H_zero_representative N τ c r s m n he]
  rw [hv] at ht
  simpa only [Finset.mul_sum] using ht

/-- Principal parts cancel at every pole, with no Fourier identity assumed. -/
lemma rawComparison_residue_zero (τ : ℍ) (c : ℂ) (hc : dilated N τ c = 0) :
    Tendsto (fun z : ℂ => z * rawComparison N τ (c + z)) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
  have hk := (kernel_sum_residue N τ c hc).const_mul (-(N : ℂ))
  have hl := logarithmic_comparison_residue N τ c hc
  have ht := hk.sub hl
  have he : -(N : ℂ) * (((if H τ c = 0 then (N : ℂ) ^ 2 else 0) - 1) / (N : ℂ)) -
      (1 - (N : ℂ) ^ 2 * (if H τ c = 0 then 1 else 0)) = 0 := by
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    split_ifs <;> field_simp [hN] <;> ring
  rw [he] at ht
  convert ht using 1
  ext z
  dsimp [rawComparison]
  ring

/-- The common entire numerator vanishes at every simple denominator zero. -/
lemma comparisonNumerator_zero (τ : ℍ) (c : ℂ) (hc : dilated N τ c = 0) :
    comparisonNumerator N τ c = 0 := by
  have hd := deriv_dilated_ne N τ c hc
  have hquot := simple_quotient_residue
    (differentiable_comparisonNumerator N τ c).continuousAt (differentiable_dilated N τ c) hc hd
  have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple (differentiable_dilated N τ c) hc hd
  have hnear : (fun z : ℂ => z * rawComparison N τ (c + z)) =ᶠ[𝓝[≠] 0]
      (fun z => z * (comparisonNumerator N τ (c + z) / dilated N τ (c + z))) := by
    have hnc : ∀ᶠ z in 𝓝[≠] 0, dilated N τ (c + z) ≠ 0 := by
      have ht : Tendsto (fun z : ℂ => c + z) (𝓝[≠] 0) (𝓝[≠] c) := by
        change Filter.map (fun z : ℂ => c + z) (𝓝[≠] 0) ≤ (𝓝[≠] c)
        rw [Filter.map_add_left_nhdsNE]
        simp
      exact ht.eventually hn
    filter_upwards [hnc] with z hz
    rw [rawComparison_eq_quotient N τ (c + z) hz]
  have he := tendsto_nhds_unique ((rawComparison_residue_zero N τ c hc).congr' hnear) hquot
  exact (div_eq_zero_iff.mp he.symm).resolve_right hd

/-- The genuine analytic extension of the complete Fourier comparison. -/
def comparison (τ : ℍ) : ℂ → ℂ := regularizedQuotient (comparisonNumerator N τ) (dilated N τ)

/-- All poles are removed by actual analytic divided differences. -/
theorem differentiable_comparison (τ : ℍ) : Differentiable ℂ (comparison N τ) := by
  apply QuasiThetaMultiplicationTwo.differentiable_regularizedQuotient
    (differentiable_comparisonNumerator N τ) (differentiable_dilated N τ)
  intro c hc
  exact ⟨comparisonNumerator_zero N τ c hc, deriv_dilated_ne N τ c hc⟩

lemma comparison_eq_raw (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    comparison N τ z = rawComparison N τ z := by
  rw [comparison, regularizedQuotient, ite_eq_right hz]
  exact (rawComparison_eq_quotient N τ z hz).symm

lemma reg_shift (a b m n : ℤ) (τ : ℍ) :
    TorsionDistributionTwo.reg N (a + (N : ℤ) * m) (b + (N : ℤ) * n) τ =
      TorsionDistributionTwo.reg N a b τ := by
  classical
  have he : ((N : ℤ) ∣ a + (N : ℤ) * m ∧ (N : ℤ) ∣ b + (N : ℤ) * n) ↔
      ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) := by
    rw [dvd_add_left (dvd_mul_right _ _), dvd_add_left (dvd_mul_right _ _)]
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [TorsionDistributionTwo.reg_of_bad (he.mpr hb), TorsionDistributionTwo.reg_of_bad hb]
  · have hs := not_congr he |>.mpr hb
    rw [TorsionDistributionTwo.reg_of_good hs, TorsionDistributionTwo.reg_of_good hb]
    exact AllLevelForms.F_shift (NeZero.pos N) hb m n τ

lemma reg_neg (a b : ℤ) (τ : ℍ) :
    TorsionDistributionTwo.reg N (-a) (-b) τ = -TorsionDistributionTwo.reg N a b τ := by
  classical
  by_cases h : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [TorsionDistributionTwo.reg_of_bad (by simpa only [Int.dvd_neg] using h),
      TorsionDistributionTwo.reg_of_bad h]
    simp
  · have hneg : ¬ ((N : ℤ) ∣ -a ∧ (N : ℤ) ∣ -b) := by simpa only [Int.dvd_neg] using h
    rw [TorsionDistributionTwo.reg_of_good hneg, TorsionDistributionTwo.reg_of_good h]
    exact AllLevelTraceTwoZeroConvention.raw_neg N (NeZero.pos N) a b h τ

lemma finite_neg_shift (a : Fin N) : ∃ m : ℤ, (((-a : Fin N) : ℕ) : ℤ) =
    -((a : ℕ) : ℤ) + (N : ℤ) * m := by
  have hmod : (((-a : Fin N) : ℕ) + (a : ℕ)) % N = 0 := by
    have h := congrArg (fun x : Fin N => (x : ℕ)) (neg_add_cancel a)
    simpa only [Fin.val_add, Fin.val_zero] using h
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hmod
  refine ⟨m, ?_⟩
  have he : (((-a : Fin N) : ℕ) : ℤ) + ((a : ℕ) : ℤ) = (N : ℤ) * m := by exact_mod_cast hm
  omega

lemma reg_finite_neg (a b : Fin N) (τ : ℍ) :
    TorsionDistributionTwo.reg N ((-a : Fin N) : ℕ) ((-b : Fin N) : ℕ) τ =
      -TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ := by
  obtain ⟨m, hm⟩ := finite_neg_shift N a
  obtain ⟨n, hn⟩ := finite_neg_shift N b
  rw [hm, hn, reg_shift, reg_neg]

/-- Oddness of the actual zero-extended family gives the zero Fourier coefficient. -/
lemma reg_sum_zero (τ : ℍ) :
    (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ) = 0 := by
  have hb (a : Fin N) :
      (∑ b : Fin N, TorsionDistributionTwo.reg N ((-a : Fin N) : ℕ) ((-b : Fin N) : ℕ) τ) =
      (∑ b : Fin N, TorsionDistributionTwo.reg N ((-a : Fin N) : ℕ) (b : ℕ) τ) := by
    exact Fintype.sum_equiv (Equiv.neg (Fin N)) _ _ (fun b => rfl)
  have hs : (∑ a : Fin N, ∑ b : Fin N,
      TorsionDistributionTwo.reg N ((-a : Fin N) : ℕ) ((-b : Fin N) : ℕ) τ) =
      (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ) := by
    simp_rw [hb]
    exact Fintype.sum_equiv (Equiv.neg (Fin N)) _ _ (fun a => rfl)
  simp_rw [reg_finite_neg, Finset.sum_neg_distrib] at hs
  linear_combination -hs / 2

lemma H_add_nat_tau_ne (τ : ℍ) (z : ℂ) (hz : H τ z ≠ 0) (k : ℕ) :
    H τ (z + (k : ℂ) * (τ : ℂ)) ≠ 0 := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
      rw [show z + ((k + 1 : ℕ) : ℂ) * (τ : ℂ) = (z + (k : ℂ) * (τ : ℂ)) + τ by push_cast; ring,
        H_add_tau]
      exact mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) ih

lemma H_log_add_nat_tau (τ : ℍ) (z : ℂ) (hz : H τ z ≠ 0) (k : ℕ) :
    ThetaWeierstrass.logDerivative (H τ) (z + (k : ℂ) * (τ : ℂ)) =
      ThetaWeierstrass.logDerivative (H τ) z - 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show z + ((k + 1 : ℕ) : ℂ) * (τ : ℂ) = (z + (k : ℂ) * (τ : ℂ)) + τ by push_cast; ring,
        ThetaWeierstrass.H_logDerivative_add_tau τ (H_add_nat_tau_ne τ z hz k), ih]
      push_cast
      ring

lemma dilated_ne_add_one (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    dilated N τ (z + 1) ≠ 0 := by
  intro h
  have hs : (N : ℂ) * (z + 1) = (N : ℂ) * z + (N : ℂ) := by ring
  have hl := (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mp h
  have hN : (N : ℂ) ∈ (ThetaWeierstrass.periodPair τ).lattice :=
    (ThetaWeierstrass.mem_periodPair_lattice_iff τ _).mpr ⟨N, 0, by simp⟩
  apply hz
  apply (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mpr
  rw [hs] at hl
  simpa using (ThetaWeierstrass.periodPair τ).lattice.sub_mem hl hN

lemma dilated_ne_add_tau (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    dilated N τ (z + (τ : ℂ)) ≠ 0 := by
  change H τ ((N : ℂ) * (z + (τ : ℂ))) ≠ 0
  rw [show (N : ℂ) * (z + (τ : ℂ)) = (N : ℂ) * z + (N : ℂ) * (τ : ℂ) by ring]
  exact H_add_nat_tau_ne τ ((N : ℂ) * z) hz N

lemma comparison_add_one_off (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    comparison N τ (z + 1) = comparison N τ z := by
  rw [comparison_eq_raw N τ (z + 1) (dilated_ne_add_one N τ z hz), comparison_eq_raw N τ z hz]
  have hper : Periodic (ThetaWeierstrass.logDerivative (H τ)) (1 : ℂ) :=
    ThetaWeierstrass.H_logDerivative_add_one τ
  have hNper := hper.nat_mul N ((N : ℂ) * z)
  simp only [rawComparison_as_logs]
  simp_rw [kernel_period_one N _ _ τ z]
  rw [show (N : ℂ) * (z + 1) = (N : ℂ) * z + (N : ℂ) * 1 by ring, hNper, hper z]

lemma comparison_add_tau_off (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    comparison N τ (z + (τ : ℂ)) = comparison N τ z := by
  rw [comparison_eq_raw N τ (z + (τ : ℂ)) (dilated_ne_add_tau N τ z hz), comparison_eq_raw N τ z hz]
  have hHz : H τ z ≠ 0 := fun h => hz (dilated_zero_of_H_zero N τ z h)
  simp only [rawComparison_as_logs]
  simp_rw [kernel_period_tau N _ _ τ z]
  rw [show (N : ℂ) * (z + (τ : ℂ)) = (N : ℂ) * z + (N : ℂ) * (τ : ℂ) by ring,
    H_log_add_nat_tau τ ((N : ℂ) * z) hz N, ThetaWeierstrass.H_logDerivative_add_tau τ hHz]
  dsimp [rawComparison, ThetaWeierstrass.logDerivative]
  simp_rw [deriv_H]
  ring

lemma comparison_periodic_of_off (τ : ℍ) (p : ℂ)
    (hoff : ∀ z : ℂ, dilated N τ z ≠ 0 → comparison N τ (z + p) = comparison N τ z) :
    Periodic (comparison N τ) p := by
  have hd := differentiable_comparison N τ
  intro c
  by_cases hc : dilated N τ c = 0
  · have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple
      (differentiable_dilated N τ c) hc (deriv_dilated_ne N τ c hc)
    have hl : Tendsto (fun z : ℂ => comparison N τ (z + p)) (𝓝[≠] c) (𝓝 (comparison N τ (c + p))) :=
      (hd.continuous.comp (continuous_id.add continuous_const)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hr : Tendsto (comparison N τ) (𝓝[≠] c) (𝓝 (comparison N τ c)) :=
      (hd c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hl.congr' (hn.mono fun z hz => hoff z hz)) hr
  · exact hoff c hc

/-- The actual, analytically regularized comparison is an elliptic entire function. -/
lemma comparison_constant (τ : ℍ) (z : ℂ) : comparison N τ z = comparison N τ 0 := by
  have hd := differentiable_comparison N τ
  have h1 := comparison_periodic_of_off N τ 1 (comparison_add_one_off N τ)
  have ht := comparison_periodic_of_off N τ (τ : ℂ) (comparison_add_tau_off N τ)
  have hb := QuasiThetaMultiplicationTwo.bounded_of_continuous_periodic hd.continuous h1 ht
  exact hd.apply_eq_apply_of_bounded hb z 0

lemma H_log_finitePart_zero (τ : ℍ) :
    Tendsto (fun z : ℂ => ThetaWeierstrass.logDerivative (H τ) z - 1 / z) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
  have hg := ThetaWeierstrass.H_logDerivative_laurent τ
  have ht : Tendsto (ThetaWeierstrass.unitLogDerivative (H τ) 0) (𝓝[≠] 0)
      (𝓝 (ThetaWeierstrass.unitLogDerivative (H τ) 0 0)) :=
    (ThetaWeierstrass.analyticAt_unitLogDerivative_zero τ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [ThetaWeierstrass.unitLogDerivative_zero] at ht
  apply ht.congr'
  filter_upwards [hg] with z hz
  change ThetaWeierstrass.unitLogDerivative (H τ) 0 z =
    ThetaWeierstrass.logDerivative (H τ) z - 1 / z
  change ThetaWeierstrass.logDerivative (H τ) z = 1 / z +
    ThetaWeierstrass.unitLogDerivative (H τ) 0 z at hz
  linear_combination -hz

lemma dilate_tendsto_zero (N : ℕ) [NeZero N] :
    Tendsto (fun z : ℂ => (N : ℂ) * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  change Filter.map (fun z : ℂ => (N : ℂ) * z) (𝓝[≠] 0) ≤ (𝓝 0) ⊓ 𝓟 {0}ᶜ
  apply le_inf
  · change Tendsto (fun z : ℂ => (N : ℂ) * z) (𝓝[≠] 0) (𝓝 0)
    have hc : ContinuousAt (fun z : ℂ => (N : ℂ) * z) 0 := by fun_prop
    simpa only [mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · rw [Filter.le_principal_iff]
    change {z : ℂ | (N : ℂ) * z ∈ {0}ᶜ} ∈ (𝓝[≠] 0)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mul_ne_zero hN hz

lemma scaled_H_log_finitePart_zero (τ : ℍ) :
    Tendsto (fun z : ℂ => (N : ℂ) * ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) * z) - 1 / z)
      (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
  have ht := ((H_log_finitePart_zero τ).comp (dilate_tendsto_zero N)).const_mul (N : ℂ)
  simp only [Function.comp_def, mul_zero] at ht
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  convert ht using 1
  · ext z
    by_cases hz : z = 0
    · simp [hz]
    · field_simp [hN, hz]

/-- The actual finite kernel sum has an independently computed Laurent finite part. -/
lemma kernel_sum_finitePart (τ : ℍ) (r s : Fin N) :
    Tendsto (fun z : ℂ => -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N,
        kernel N (a : ℕ) (b : ℕ) τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) -
        (1 - if r = 0 ∧ s = 0 then (N : ℂ) ^ 2 else 0) / z)
      (𝓝[≠] 0) (𝓝 (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
        (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
          character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)))) := by
  classical
  let C : Fin N → Fin N → ℂ := fun a b =>
    if a = 0 ∧ b = 0 then 0 else character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)
  have hterm (a b : Fin N) :
      Tendsto (fun z : ℂ => kernel N (a : ℕ) (b : ℕ) τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ) -
          C a b / ((N : ℂ) * z)) (𝓝[≠] 0)
        (𝓝 (-2 * (Real.pi : ℂ) * Complex.I * TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
          character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ))) := by
    by_cases hab : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hab
      simp [C, kernel_zero_row, TorsionDistributionTwo.reg, character]
    · have hg := (finite_good_iff N a b).mpr (by tauto)
      dsimp [C]
      rw [ite_eq_right hab]
      simpa only [character, Int.cast_natCast] using kernel_finitePart_torsion N (a : ℕ) (b : ℕ) τ hg r s
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun a _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun b _ => hterm a b))
  have hC : (∑ a : Fin N, ∑ b : Fin N, C a b) =
      (if r = 0 ∧ s = 0 then (N : ℂ) ^ 2 else 0) - 1 := by
    change (∑ a : Fin N, ∑ b : Fin N,
      if a = 0 ∧ b = 0 then (0 : ℂ) else character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) = _
    rw [character_sum_nonzero]
    have hd : (N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ) ↔ r = 0 ∧ s = 0 := by
      have h := not_congr (finite_good_iff N r s)
      simpa only [not_not, not_or] using h
    simp only [hd]
  have hlim : (∑ a : Fin N, ∑ b : Fin N,
      -2 * (Real.pi : ℂ) * Complex.I * TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) =
      -2 * (Real.pi : ℂ) * Complex.I * (∑ a : Fin N, ∑ b : Fin N,
        TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) := by
    simp only [mul_assoc]
    simp_rw [← Finset.mul_sum]
  rw [hlim] at ht
  have ht' := ht.const_mul (-(N : ℂ))
  convert ht' using 1
  · ext z
    simp_rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    rw [hC]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    by_cases hz : z = 0
    · simp [hz]
    · split_ifs <;> field_simp [hN, hz] <;> ring
  · ring

lemma rawComparison_tendsto_zero (τ : ℍ) :
    Tendsto (rawComparison N τ) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
  have hk := kernel_sum_finitePart N τ (0 : Fin N) (0 : Fin N)
  simp [character, torsionPoint] at hk
  rw [reg_sum_zero N τ, mul_zero] at hk
  have ht := (hk.sub (scaled_H_log_finitePart_zero N τ)).add
    ((H_log_finitePart_zero τ).const_mul ((N : ℂ) ^ 2))
  convert ht using 1
  · ext z
    dsimp [rawComparison, ThetaWeierstrass.logDerivative]
    simp_rw [deriv_H]
    ring
  · simp

/-- The independently computed zero Laurent constant fixes the entire comparison. -/
lemma comparison_zero (τ : ℍ) : comparison N τ 0 = 0 := by
  have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple
    (differentiable_dilated N τ 0) (by simp [dilated, H_zero])
    (deriv_dilated_ne N τ 0 (by simp [dilated, H_zero]))
  have he : comparison N τ =ᶠ[𝓝[≠] 0] rawComparison N τ :=
    hn.mono (fun z hz => comparison_eq_raw N τ z hz)
  have ht : Tendsto (comparison N τ) (𝓝[≠] 0) (𝓝 (comparison N τ 0)) :=
    (differentiable_comparison N τ 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (ht.congr' he) (rawComparison_tendsto_zero N τ)

/-- The genuine regularized global comparison vanishes identically. -/
theorem comparison_eq_zero (τ : ℍ) (z : ℂ) : comparison N τ z = 0 := by
  rw [comparison_constant N τ z, comparison_zero N τ]

/-- The actual global meromorphic kernel identity, away from its actual pole set. -/
theorem global_kernel_comparison (τ : ℍ) (z : ℂ) (hz : dilated N τ z ≠ 0) :
    -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N, kernel N (a : ℕ) (b : ℕ) τ z) =
      (N : ℂ) * (Hder τ ((N : ℂ) * z) / H τ ((N : ℂ) * z)) -
        (N : ℂ) ^ 2 * (Hder τ z / H τ z) := by
  have h := comparison_eq_zero N τ z
  rw [comparison_eq_raw N τ z hz] at h
  dsimp [rawComparison] at h
  linear_combination h

lemma reg_eq_logDerivative (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    TorsionDistributionTwo.reg N a b τ = (a : ℂ) / (N : ℂ) +
      ThetaWeierstrass.logDerivative (H τ) (torsionPoint N a b τ) / (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [TorsionDistributionTwo.reg_of_good hg, torsionLogDerivative_eq_deriv N (NeZero.pos N) τ a b hg]
  dsimp [ThetaWeierstrass.logDerivative]
  rw [div_div]
  ring

lemma torsion_dilated_zero (τ : ℍ) (r s : Fin N) :
    dilated N τ (torsionPoint N (r : ℕ) (s : ℕ) τ) = 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (N : ℂ) * torsionPoint N (r : ℕ) (s : ℕ) τ =
      ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) := by
    dsimp [torsionPoint]
    push_cast
    field_simp
  change H τ ((N : ℂ) * torsionPoint N (r : ℕ) (s : ℕ) τ) = 0
  rw [hp]
  apply (CompletedTheta.H_zero_iff_lattice τ _).mpr
  exact ⟨s, r, by push_cast; ring⟩

lemma logarithmic_finitePart_torsion (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    Tendsto (fun z : ℂ => (N : ℂ) * (Hder τ ((N : ℂ) * (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) /
        H τ ((N : ℂ) * (z + torsionPoint N (r : ℕ) (s : ℕ) τ))) -
        (N : ℂ) ^ 2 * (Hder τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ) /
          H τ (z + torsionPoint N (r : ℕ) (s : ℕ) τ)) - 1 / z)
      (𝓝[≠] 0) (𝓝 (-2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) ^ 2 *
        TorsionDistributionTwo.reg N (r : ℕ) (s : ℕ) τ)) := by
  let t := torsionPoint N (r : ℕ) (s : ℕ) τ
  have hH := H_torsion_ne_zero N (NeZero.pos N) τ (r : ℕ) (s : ℕ) hg
  have hcont : ContinuousAt (fun z : ℂ => ThetaWeierstrass.logDerivative (H τ) (z + t)) 0 := by
    have hh : ContinuousAt (ThetaWeierstrass.logDerivative (H τ)) (0 + t) := by
      simpa using (ThetaWeierstrass.analyticAt_logDerivative (differentiable_H τ) hH).continuousAt
    have hAdd : ContinuousAt (fun z : ℂ => z + t) 0 := by fun_prop
    exact ContinuousAt.comp' (f := fun z : ℂ => z + t) (x := (0 : ℂ)) hh hAdd
  have htlog : Tendsto (fun z : ℂ => ThetaWeierstrass.logDerivative (H τ) (z + t)) (𝓝[≠] 0)
      (𝓝 (ThetaWeierstrass.logDerivative (H τ) t)) := by
    simpa only [zero_add] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hvalue : (0 : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ) -
      (N : ℂ) ^ 2 * ThetaWeierstrass.logDerivative (H τ) t =
      -2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) ^ 2 * TorsionDistributionTwo.reg N (r : ℕ) (s : ℕ) τ := by
    rw [reg_eq_logDerivative N (r : ℕ) (s : ℕ) τ hg]
    dsimp [t]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    push_cast
    field_simp [hN, hc]
    ring
  have ht := ((scaled_H_log_finitePart_zero N τ).sub_const
    (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ))).sub
    (htlog.const_mul ((N : ℂ) ^ 2))
  rw [hvalue] at ht
  have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple (differentiable_dilated N τ 0)
    (by simp [dilated, H_zero]) (deriv_dilated_ne N τ 0 (by simp [dilated, H_zero]))
  have he : (fun z : ℂ => (N : ℂ) * (Hder τ ((N : ℂ) * (z + t)) / H τ ((N : ℂ) * (z + t))) -
        (N : ℂ) ^ 2 * (Hder τ (z + t) / H τ (z + t)) - 1 / z) =ᶠ[𝓝[≠] 0]
      (fun z => ((N : ℂ) * ThetaWeierstrass.logDerivative (H τ) ((N : ℂ) * z) - 1 / z) -
        2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * ((r : ℕ) : ℂ) -
          (N : ℂ) ^ 2 * ThetaWeierstrass.logDerivative (H τ) (z + t)) := by
    filter_upwards [hn] with z hz
    have hp : (N : ℂ) * (z + t) = (N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) := by
      dsimp [t, torsionPoint]
      push_cast
      have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      field_simp [hN]
      ring
    have hper : Periodic (ThetaWeierstrass.logDerivative (H τ)) (1 : ℂ) :=
      ThetaWeierstrass.H_logDerivative_add_one τ
    have hs := hper.nat_mul (s : ℕ) ((N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ))
    have hlogeq (w : ℂ) : Hder τ w / H τ w = ThetaWeierstrass.logDerivative (H τ) w := by
      dsimp [ThetaWeierstrass.logDerivative]
      rw [deriv_H]
    simp only [hlogeq]
    rw [hp, show (N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) =
      (N : ℂ) * z + ((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ) * 1 by ring, hs,
      H_log_add_nat_tau τ ((N : ℂ) * z) hz (r : ℕ)]
    ring
  exact ht.congr' he.symm

/-- Fourier duality recovered from the actual global comparison, for a nonzero finite label. -/
lemma fourier_duality_finite_good (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    TorsionDistributionTwo.reg N (r : ℕ) (s : ℕ) τ = -(1 / (N : ℂ)) *
      (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) := by
  have hnot : ¬ (r = 0 ∧ s = 0) := by have h := (finite_good_iff N r s).mp hg; tauto
  have hk := kernel_sum_finitePart N τ r s
  rw [ite_eq_right hnot, sub_zero] at hk
  have hr := logarithmic_finitePart_torsion N τ r s hg
  let t := torsionPoint N (r : ℕ) (s : ℕ) τ
  have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple
    (differentiable_dilated N τ t) (torsion_dilated_zero N τ r s)
    (deriv_dilated_ne N τ t (torsion_dilated_zero N τ r s))
  have htranslate : Tendsto (fun z : ℂ => z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    change Filter.map (fun z : ℂ => z + t) (𝓝[≠] 0) ≤ (𝓝[≠] t)
    rw [Filter.map_add_right_nhdsNE]
    simp
  have hnear : (fun z : ℂ => -(N : ℂ) * (∑ a : Fin N, ∑ b : Fin N,
      kernel N (a : ℕ) (b : ℕ) τ (z + t)) - 1 / z) =ᶠ[𝓝[≠] 0]
    (fun z => (N : ℂ) * (Hder τ ((N : ℂ) * (z + t)) / H τ ((N : ℂ) * (z + t))) -
      (N : ℂ) ^ 2 * (Hder τ (z + t) / H τ (z + t)) - 1 / z) := by
    filter_upwards [htranslate.eventually hn] with z hz
    rw [global_kernel_comparison N τ (z + t) hz]
  have he := tendsto_nhds_unique (hk.congr' hnear) hr
  have hc : (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hsum : (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
      character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) =
      -(N : ℂ) * TorsionDistributionTwo.reg N (r : ℕ) (s : ℕ) τ := by
    apply mul_left_cancel₀ hc
    linear_combination he
  rw [hsum]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hN]

/-- Actual Fourier duality for all finite torsion representatives, with zero extension. -/
theorem fourier_duality_finite (τ : ℍ) (r s : Fin N) :
    TorsionDistributionTwo.reg N (r : ℕ) (s : ℕ) τ = -(1 / (N : ℂ)) *
      (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) := by
  by_cases hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))
  · exact fourier_duality_finite_good N τ r s hg
  · have hzero : r = 0 ∧ s = 0 := by have h := (finite_good_iff N r s).not.mp hg; tauto
    obtain ⟨rfl, rfl⟩ := hzero
    simp only [Fin.val_zero]
    rw [TorsionDistributionTwo.reg_of_bad (by simp)]
    simp [character, reg_sum_zero N τ]

lemma character_shift (a b r s m n : ℤ) :
    character N a b (r + (N : ℤ) * m) (s + (N : ℤ) * n) = character N a b r s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have he : 2 * (Real.pi : ℂ) * Complex.I *
      ((b : ℂ) * (r + (N : ℤ) * m : ℤ) - (a : ℂ) * (s + (N : ℤ) * n : ℤ)) / (N : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * ((b : ℂ) * r - (a : ℂ) * s) / (N : ℂ) +
        ((b * m - a * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hN]
    ring
  unfold character
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The unrestricted integer-label endpoint, with its exact orientation and normalizing factor. -/
theorem torsion_fourier_duality (τ : ℍ) (r s : ℤ) :
    TorsionDistributionTwo.reg N r s τ = -(1 / (N : ℂ)) *
      (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((b : ℕ) : ℂ) * (r : ℂ) - ((a : ℕ) : ℂ) * (s : ℂ)) / (N : ℂ))) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNz : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  let R : Fin N := ⟨(r % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg r hN0
    have h1 := Int.emod_lt_of_pos r hNz
    omega⟩
  let S : Fin N := ⟨(s % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg s hN0
    have h1 := Int.emod_lt_of_pos s hNz
    omega⟩
  have hR : ((R : ℕ) : ℤ) = r % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg r hN0)
  have hS : ((S : ℕ) : ℤ) = s % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg s hN0)
  have hr : r = ((R : ℕ) : ℤ) + (N : ℤ) * (r / (N : ℤ)) := by
    rw [hR]
    exact (Int.emod_add_mul_ediv r (N : ℤ)).symm
  have hs : s = ((S : ℕ) : ℤ) + (N : ℤ) * (s / (N : ℤ)) := by
    rw [hS]
    exact (Int.emod_add_mul_ediv s (N : ℤ)).symm
  change TorsionDistributionTwo.reg N r s τ = -(1 / (N : ℂ)) *
      (∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        character N (a : ℕ) (b : ℕ) r s)
  rw [hr, hs, reg_shift]
  simp_rw [character_shift]
  exact fourier_duality_finite N τ R S

end ZInQ.Contrib.HeckePrimeRationality.TorsionFourierComparison
