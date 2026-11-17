import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationNat

/-!
# Torsion distribution in every positive degree

For positive integers `n`, `N` and integers `a, b` not both divisible by `N`, all `n²` labels
`(a + N r, b + N s)`, `r, s ∈ {0, …, n-1}`, are admissible at level `n N`, and
`Σ_{r,s} F_{nN}(a + N r, b + N s) = n F_N(a, b)`, where `F = Torsion.torsionLogDerivative`.

Proof. The completed theta function satisfies
`∏_{r,s} H(z + (r τ + s)/n) = C exp(-π i n (n-1) z) H(n z)` with `C ≠ 0`. The logarithmic
derivative of this identity at `z = u = (a τ + b)/(nN)`, where all factors are nonzero, gives
`Σ_{r,s} H'/H(u + (r τ + s)/n) = -π i n (n-1) + n H'(nu)/H(nu)`. With
`F_M(a, b) = a/M + H'(t)/(2π i H(t))` at the torsion point `t`, the completion terms contribute
`Σ_{r,s} (a + N r)/(nN) = n a/N + n(n-1)/2`, cancelling `-π i n(n-1)/(2π i)`.

The multiplication identity is the proved `H_multiplication_nat`; nothing is assumed.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionNat

open CompletedTheta

/-- Logarithmic derivative of a finite product with nonvanishing factors. -/
theorem hasDerivAt_prod_logDeriv {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℂ → ℂ}
    {f' : ι → ℂ} {z : ℂ} (hf : ∀ i, HasDerivAt (f i) (f' i) z) (h0 : ∀ i, f i z ≠ 0) :
    HasDerivAt (fun x => ∏ i, f i x) ((∏ i, f i z) * ∑ i, f' i / f i z) z := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have := h0 i
  field_simp

/-- The `1/n`-lattice shifts `(r τ + s)/n`. -/
def cn (τ : ℍ) (n : ℕ) (p : Fin n × Fin n) : ℂ :=
  (((p.1 : ℕ) : ℂ) * (τ : ℂ) + ((p.2 : ℕ) : ℂ)) / (n : ℂ)

/-- The constant of the logarithmic derivative of the exponential factor. -/
def K (n : ℕ) : ℂ := -(π : ℂ) * I * (n : ℂ) * ((n - 1 : ℕ) : ℂ)

/-- Logarithmic derivative of the degree-`n` multiplication identity. -/
theorem logDeriv_sum (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) (hz : ∀ p, H τ (z + cn τ n p) ≠ 0)
    (hnz : H τ ((n : ℂ) * z) ≠ 0) :
    ∑ p, Hder τ (z + cn τ n p) / H τ (z + cn τ n p) =
      K n + (n : ℂ) * (Hder τ ((n : ℂ) * z) / H τ ((n : ℂ) * z)) := by
  obtain ⟨C, hC, hid⟩ := H_multiplication_nat n hn τ
  set L : ℂ → ℂ := fun x => ∏ p, H τ (x + cn τ n p) with hLdef
  have hLeq : ∀ x, L x = C * cexp (K n * x) * H τ ((n : ℂ) * x) := by
    intro x
    have h := hid x
    rw [← Fintype.prod_prod_type'] at h
    simpa only [hLdef, K, cn] using h
  have hL : HasDerivAt L (L z * ∑ p, Hder τ (z + cn τ n p) / H τ (z + cn τ n p)) z :=
    hasDerivAt_prod_logDeriv (f := fun p x => H τ (x + cn τ n p))
      (fun p => (hasDerivAt_H τ (z + cn τ n p)).comp_add_const z _) hz
  have he : HasDerivAt (fun x : ℂ => cexp (K n * x)) (cexp (K n * z) * K n) z := by
    simpa using ((hasDerivAt_id z).const_mul (K n)).cexp
  have hd : HasDerivAt (fun x : ℂ => H τ ((n : ℂ) * x)) (Hder τ ((n : ℂ) * z) * (n : ℂ)) z := by
    have h := (hasDerivAt_H τ ((n : ℂ) * z)).comp z ((hasDerivAt_id' z).const_mul (n : ℂ))
    exact h.congr_deriv (by ring)
  have hR : HasDerivAt L (C * (cexp (K n * z) * K n) * H τ ((n : ℂ) * z) +
      C * cexp (K n * z) * (Hder τ ((n : ℂ) * z) * (n : ℂ))) z := by
    have hfun : L = fun x => C * cexp (K n * x) * H τ ((n : ℂ) * x) := funext hLeq
    rw [hfun]
    exact (he.const_mul C).mul hd
  have hderiv := hL.unique hR
  have hval := hLeq z
  set S := ∑ p, Hder τ (z + cn τ n p) / H τ (z + cn τ n p) with hS
  have hCE : C * cexp (K n * z) ≠ 0 := mul_ne_zero hC (Complex.exp_ne_zero _)
  generalize L z = Lz at hderiv hval
  generalize H τ ((n : ℂ) * z) = h at hderiv hval hnz ⊢
  generalize Hder τ ((n : ℂ) * z) = h' at hderiv ⊢
  generalize cexp (K n * z) = E at hderiv hval hCE
  have key : (C * E) * (S * h) = (C * E) * (K n * h + (n : ℂ) * h') := by
    linear_combination hderiv - S * hval
  have key' := mul_left_cancel₀ hCE key
  field_simp
  linear_combination key'

/-- Admissibility of the `n²` preimages at level `n N`. -/
theorem good_preimage {n N : ℕ} {a b : ℤ} (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (r s : Fin n) :
    ¬ (((n * N : ℕ) : ℤ) ∣ a + N * ((r : ℕ) : ℤ) ∧ ((n * N : ℕ) : ℤ) ∣ b + N * ((s : ℕ) : ℤ)) := by
  rintro ⟨h1, h2⟩
  apply hg
  have hd : (N : ℤ) ∣ ((n * N : ℕ) : ℤ) := ⟨n, by push_cast; ring⟩
  exact ⟨(dvd_add_left (dvd_mul_right _ _)).mp (hd.trans h1),
    (dvd_add_left (dvd_mul_right _ _)).mp (hd.trans h2)⟩

theorem torsionPoint_preimage {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (a b : ℤ) (τ : ℍ)
    (r s : Fin n) :
    torsionPoint (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      torsionPoint N a b τ / n + cn τ n (r, s) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold torsionPoint cn
  push_cast
  field_simp
  ring

/-- Gauss's sum over `Fin n`. -/
theorem sum_fin_cast (n : ℕ) : ∑ r : Fin n, ((r : ℕ) : ℂ) = (n : ℂ) * ((n - 1 : ℕ) : ℂ) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℂ)) n]
  have h := Finset.sum_range_id_mul_two n
  have h' : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by
    exact_mod_cast h
  rw [Nat.cast_sum, Nat.cast_mul] at h'
  linear_combination h' / 2

/-- **Torsion distribution in degree `n`** for admissible labels. -/
theorem distribution_nat (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∑ r : Fin n, ∑ s : Fin n,
        Torsion.torsionLogDerivative (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      (n : ℂ) * Torsion.torsionLogDerivative N a b τ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnN : 0 < n * N := Nat.mul_pos hn hN
  set t := torsionPoint N a b τ with ht
  set u := t / n with hu
  have hnu : (n : ℂ) * u = t := by rw [hu]; field_simp
  have hz : ∀ p : Fin n × Fin n, H τ (u + cn τ n p) ≠ 0 := by
    intro p
    rw [hu, ← torsionPoint_preimage hn hN a b τ p.1 p.2]
    exact H_torsion_ne_zero (n * N) hnN τ _ _ (good_preimage hg p.1 p.2)
  have ht0 : H τ t ≠ 0 := H_torsion_ne_zero N hN τ a b hg
  have hls := logDeriv_sum n hn τ u hz (by rw [hnu]; exact ht0)
  rw [hnu] at hls
  have hterm : ∀ r s : Fin n,
      Torsion.torsionLogDerivative (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
        ((a + N * ((r : ℕ) : ℤ) : ℤ) : ℂ) / ((n * N : ℕ) : ℂ) +
          Hder τ (u + cn τ n (r, s)) / (2 * π * I * H τ (u + cn τ n (r, s))) := by
    intro r s
    rw [torsionLogDerivative_eq (n * N) hnN τ _ _ (good_preimage hg r s),
      torsionPoint_preimage hn hN a b τ r s]
  simp_rw [hterm]
  simp_rw [Finset.sum_add_distrib]
  have hX : ∑ r : Fin n, ∑ _s : Fin n, ((a + N * ((r : ℕ) : ℤ) : ℤ) : ℂ) / ((n * N : ℕ) : ℂ) =
      (n : ℂ) * a / N + (n : ℂ) * ((n - 1 : ℕ) : ℂ) / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    push_cast
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, sum_fin_cast n]
    field_simp
  have hY : ∑ r : Fin n, ∑ s : Fin n,
      Hder τ (u + cn τ n (r, s)) / (2 * π * I * H τ (u + cn τ n (r, s))) =
      (∑ p, Hder τ (u + cn τ n p) / H τ (u + cn τ n p)) / (2 * π * I) := by
    rw [← Fintype.sum_prod_type' (fun r s =>
      Hder τ (u + cn τ n (r, s)) / (2 * π * I * H τ (u + cn τ n (r, s)))), Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := hz p
    field_simp
  rw [hX, hY, hls, torsionLogDerivative_eq N hN τ a b hg, ← ht, K]
  field_simp
  ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionNat
