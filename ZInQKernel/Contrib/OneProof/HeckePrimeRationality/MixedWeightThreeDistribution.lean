import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedWeightThreeAddition
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuDistributionNat

/-!
# Weight-three distribution congruences

At level `nN`, for integer labels `A = (a, b)`, `C = (c, d)` and the `n`-torsion shifts
`T = (N r, N s)`, `r, s < n`, both of the following lie in the span of the convergent weight-three
congruence-class series forms:

* `∑_T x_{A+T} λ_{A+T} - n · x_{nA} λ_{nA}` (`xlam_distribution_mem`);
* `∑_T x_{A+T} λ_{C-T} - (-n x_{nA} λ_{nA} + n² x_{nA} λ_{A+C} + n x_{A+C} λ_{nA}
  + n x_{A+C} λ_{nC} - n² x_{A+C} λ_{A+C})` (`cross_distribution_mem`).

Here `nA` denotes the level-`nN` label `(na, nb)`, whose values are the level-`N` values at `A`.

Proof: sum the mixed addition forms (each in the series span) over `P = A + T`, `Q = -A + U`,
respectively over `P = A + T`, `Q = C - T`. The summed values are computed exactly with the
`x`-distribution (constant `n²`), the `λ`-distribution (constant `n`), the vanishing of both at
torsion-divisible base labels, a periodic reindexing and the oddness of `x λ`; no degenerate term
is dropped.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeDistribution

open TorsionWeierstrassData TorsionWeightThree MixedWeightThreeAddition

/-! ### Finite sums -/

theorem shift_fin (n : ℕ) (h : ℤ → ℤ → ℂ) (hp1 : ∀ u v, h (u + n) v = h u v)
    (hp2 : ∀ u v, h u (v + n) = h u v) (r s : ℤ) :
    (∑ r' : Fin n, ∑ s' : Fin n, h (((r' : ℕ) : ℤ) + r) (((s' : ℕ) : ℤ) + s)) =
      ∑ r' : Fin n, ∑ s' : Fin n, h ((r' : ℕ) : ℤ) ((s' : ℕ) : ℤ) := by
  have inner : ∀ u : ℤ, (∑ s' : Fin n, h u (((s' : ℕ) : ℤ) + s)) =
      ∑ s' : Fin n, h u ((s' : ℕ) : ℤ) := fun u => by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => h u ((j : ℤ) + s)) n,
      Fin.sum_univ_eq_sum_range (fun j : ℕ => h u (j : ℤ)) n]
    exact AllLevelAverage.sum_range_shift (N := n) (fun m => h u m) (fun m => hp2 u m) s
  simp_rw [inner]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ s' : Fin n, h ((j : ℤ) + r) ((s' : ℕ) : ℤ)) n,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ s' : Fin n, h (j : ℤ) ((s' : ℕ) : ℤ)) n]
  exact AllLevelAverage.sum_range_shift (N := n) (fun m => ∑ s' : Fin n, h m ((s' : ℕ) : ℤ))
    (fun m => Finset.sum_congr rfl fun s' _ => hp1 m _) r

variable {n N : ℕ}

theorem x_sum_bad (hn : 0 < n) (hN : 0 < N) (u v : ℤ) (hu : (N : ℤ) ∣ u) (hv : (N : ℤ) ∣ v)
    (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      xValue (n * N) (u + N * ((r : ℕ) : ℤ)) (v + N * ((s : ℕ) : ℤ)) τ) = 0 := by
  rw [WeierstrassDistributionNat.x_distribution_nat n N hn hN τ u v]
  simp [xValue, hu, hv]

theorem lam_sum (hn : 0 < n) (hN : 0 < N) (u v : ℤ) (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      lambdaValue (n * N) (u + N * ((r : ℕ) : ℤ)) (v + N * ((s : ℕ) : ℤ)) τ) =
      (n : ℂ) * lambdaValue N u v τ := by
  unfold lambdaValue
  simp_rw [← Finset.mul_sum]
  rw [TorsionDistributionNat.reg_distribution_nat n N hn hN τ u v]
  ring

theorem lam_sum_bad (hn : 0 < n) (hN : 0 < N) (u v : ℤ) (hu : (N : ℤ) ∣ u) (hv : (N : ℤ) ∣ v)
    (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      lambdaValue (n * N) (u + N * ((r : ℕ) : ℤ)) (v + N * ((s : ℕ) : ℤ)) τ) = 0 := by
  rw [lam_sum hn hN, lambdaValue, TorsionDistributionTwo.reg_of_bad ⟨hu, hv⟩]
  ring

/-- The values `x λ` at level `nN` on the `n`-torsion sum to zero. -/
theorem xlam_torsion_sum_zero (hn : 0 < n) (hN : 0 < N) (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      xValue (n * N) (N * ((r : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ)) τ *
        lambdaValue (n * N) (N * ((r : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ)) τ) = 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n * N) := ⟨(Nat.mul_pos hn hN).ne'⟩
  have hM : 0 < n * N := Nat.mul_pos hn hN
  let f : ℤ → ℤ → ℂ := fun u v =>
    xValue (n * N) (N * u) (N * v) τ * lambdaValue (n * N) (N * u) (N * v) τ
  have hsh : ∀ u v m k : ℤ, f (u + n * m) (v + n * k) = f u v := by
    intro u v m k
    have e1 : (N : ℤ) * (u + n * m) = N * u + ((n * N : ℕ) : ℤ) * m := by push_cast; ring
    have e2 : (N : ℤ) * (v + n * k) = N * v + ((n * N : ℕ) : ℤ) * k := by push_cast; ring
    simp only [f, lambdaValue]
    rw [e1, e2, WeierstrassDistributionNat.xValue_shift hM, TorsionFourierComparison.reg_shift]
  have hodd : ∀ u v : ℤ, f (-u) (-v) = -f u v := by
    intro u v
    simp only [f, lambdaValue, mul_neg]
    rw [TorsionWeightThree.xValue_neg (n * N), TorsionFourierComparison.reg_neg]
    ring
  have h0 := TorsionWeightThree.finite_sum_odd n f hsh hodd
  rw [Fintype.sum_prod_type] at h0
  exact h0

/-! ### The summed mixed values -/

theorem summed_mixed_value (hn : 0 < n) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      (xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ -
          xValue (n * N) ((a + N * ((r : ℕ) : ℤ)) + (-a + N * ((r' : ℕ) : ℤ)))
            ((b + N * ((s : ℕ) : ℤ)) + (-b + N * ((s' : ℕ) : ℤ))) τ) *
        (lambdaValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ +
          lambdaValue (n * N) (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) τ -
          lambdaValue (n * N) ((a + N * ((r : ℕ) : ℤ)) + (-a + N * ((r' : ℕ) : ℤ)))
            ((b + N * ((s : ℕ) : ℤ)) + (-b + N * ((s' : ℕ) : ℤ))) τ)) =
      (n : ℂ) ^ 2 * ∑ r : Fin n, ∑ s : Fin n,
          xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ *
            lambdaValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ -
        (n : ℂ) ^ 3 * (xValue N a b τ * lambdaValue N a b τ) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (n * N) := ⟨(Nat.mul_pos hn hN).ne'⟩
  have hM : 0 < n * N := Nat.mul_pos hn hN
  simp_rw [show ∀ x y : ℤ, (a + x) + (-a + y) = x + y from fun x y => by ring,
    show ∀ x y : ℤ, (b + x) + (-b + y) = x + y from fun x y => by ring]
  -- notation
  set X : ℤ → ℤ → ℂ := fun u v => xValue (n * N) u v τ with hX
  set Lm : ℤ → ℤ → ℂ := fun u v => lambdaValue (n * N) u v τ with hL
  change (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      (X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) -
          X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) *
        (Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
          Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) -
          Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)))) =
    (n : ℂ) ^ 2 * ∑ r : Fin n, ∑ s : Fin n,
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) -
      (n : ℂ) ^ 3 * (xValue N a b τ * lambdaValue N a b τ)
  -- the six partial sums
  have hT1 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
        Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) =
      (n : ℂ) ^ 2 * ∑ r : Fin n, ∑ s : Fin n,
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hT2 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
        Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ))) =
      -((n : ℂ) ^ 3 * (xValue N a b τ * lambdaValue N a b τ)) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [lam_sum hn hN, WeierstrassDistributionNat.x_distribution_nat n N hn hN τ a b]
    rw [show lambdaValue N (-a) (-b) τ = -lambdaValue N a b τ by
      unfold lambdaValue; rw [TorsionFourierComparison.reg_neg]; ring]
    ring
  have hT3 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
        Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) = 0 := by
    simp_rw [← Finset.mul_sum]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    rw [lam_sum_bad hn hN _ _ (dvd_mul_right _ _) (dvd_mul_right _ _), mul_zero]
  have hT4 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
        Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) = 0 := by
    simp_rw [← Finset.sum_mul]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    rw [x_sum_bad hn hN _ _ (dvd_mul_right _ _) (dvd_mul_right _ _), zero_mul]
  have hT5 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
        Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ))) = 0 := by
    rw [TorsionMuDistributionNat.swap4]
    simp_rw [← Finset.sum_mul, show ∀ x y : ℤ, (N : ℤ) * x + N * y = N * y + N * x from
      fun x y => by ring]
    refine Finset.sum_eq_zero fun r' _ => Finset.sum_eq_zero fun s' _ => ?_
    rw [x_sum_bad hn hN _ _ (dvd_mul_right _ _) (dvd_mul_right _ _), zero_mul]
  have hT6 : (∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
      X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
        Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) = 0 := by
    let g : ℤ → ℤ → ℂ := fun u v => X (N * u) (N * v) * Lm (N * u) (N * v)
    have hp1 : ∀ u v, g (u + n) v = g u v := by
      intro u v
      have e : (N : ℤ) * (u + n) = N * u + ((n * N : ℕ) : ℤ) := by push_cast; ring
      have h1 := WeierstrassDistributionNat.xValue_shift hM (N * u) (N * v) 1 0 τ
      have h2 := TorsionFourierComparison.reg_shift (n * N) (N * u) (N * v) 1 0 τ
      simp only [mul_one, mul_zero, add_zero] at h1 h2
      simp only [g, hX, hL, lambdaValue]
      rw [e, h1, h2]
    have hp2 : ∀ u v, g u (v + n) = g u v := by
      intro u v
      have e : (N : ℤ) * (v + n) = N * v + ((n * N : ℕ) : ℤ) := by push_cast; ring
      have h1 := WeierstrassDistributionNat.xValue_shift hM (N * u) (N * v) 0 1 τ
      have h2 := TorsionFourierComparison.reg_shift (n * N) (N * u) (N * v) 0 1 τ
      simp only [mul_one, mul_zero, add_zero] at h1 h2
      simp only [g, hX, hL, lambdaValue]
      rw [e, h1, h2]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    have hs := shift_fin n g hp1 hp2 ((r : ℕ) : ℤ) ((s : ℕ) : ℤ)
    have hz := xlam_torsion_sum_zero hn hN τ
    have hl : (∑ r' : Fin n, ∑ s' : Fin n,
        X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
          Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) =
        ∑ r' : Fin n, ∑ s' : Fin n, g (((r' : ℕ) : ℤ) + ((r : ℕ) : ℤ)) (((s' : ℕ) : ℤ) + ((s : ℕ) : ℤ)) := by
      refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun s' _ => ?_
      simp only [g]
      rw [show (N : ℤ) * (((r' : ℕ) : ℤ) + ((r : ℕ) : ℤ)) = N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ) by ring,
        show (N : ℤ) * (((s' : ℕ) : ℤ) + ((s : ℕ) : ℤ)) = N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ) by ring]
    rw [hl, hs]
    exact hz
  have hexp : ∀ r s r' s' : Fin n,
      (X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) -
          X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) *
        (Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
          Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) -
          Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ))) =
      X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) -
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) -
        X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
          Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) -
        X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
          Lm (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) +
        X (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) *
          Lm (N * ((r : ℕ) : ℤ) + N * ((r' : ℕ) : ℤ)) (N * ((s : ℕ) : ℤ) + N * ((s' : ℕ) : ℤ)) :=
    fun _ _ _ _ => by ring
  simp_rw [hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT1, hT2, hT3, hT4, hT5, hT6]
  ring

/-! ### Forms -/

/-- The weight-three form `x_{(u,v)} λ_{(u,v)}`. -/
def xlamForm (M : ℕ) (hM : 0 < M) (u v : ℤ) : Weight M 3 :=
  lambdaTimesForm M hM u v (WeierstrassForms.xForm M hM u v)

theorem xlamForm_apply (M : ℕ) (hM : 0 < M) (u v : ℤ) (τ : ℍ) :
    xlamForm M hM u v τ = xValue M u v τ * lambdaValue M u v τ := by
  rw [xlamForm, lambdaTimesForm_apply, WeierstrassForms.xForm_apply]
  ring

/-- **First weight-three distribution congruence** (the relation (4.40) of the reference),
for every integer label and all positive `n, N`. -/
theorem xlam_distribution_mem (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b : ℤ) :
    (∑ r : Fin n, ∑ s : Fin n,
        xlamForm (n * N) (Nat.mul_pos hn hN) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) -
      (n : ℂ) • xlamForm (n * N) (Nat.mul_pos hn hN) ((n : ℤ) * a) ((n : ℤ) * b) ∈
      classSeriesSpan (n * N) (Nat.mul_pos hn hN) := by
  have hM : 0 < n * N := Nat.mul_pos hn hN
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (n * N) := ⟨hM.ne'⟩
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set S4 : Weight (n * N) 3 := ∑ r : Fin n, ∑ s : Fin n, ∑ r' : Fin n, ∑ s' : Fin n,
    mixedForm (n * N) hM (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))
      (-a + N * ((r' : ℕ) : ℤ)) (-b + N * ((s' : ℕ) : ℤ)) with hS4
  have hmem : S4 ∈ classSeriesSpan (n * N) hM :=
    Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ =>
      Submodule.sum_mem _ fun r' _ => Submodule.sum_mem _ fun s' _ => mixedForm_mem _ _ _ _ _ _
  have heq : S4 = ((n : ℂ) ^ 2) •
      ((∑ r : Fin n, ∑ s : Fin n,
        xlamForm (n * N) hM (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) -
      (n : ℂ) • xlamForm (n * N) hM ((n : ℤ) * a) ((n : ℤ) * b)) := by
    apply DFunLike.ext
    intro τ
    rw [hS4]
    simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul, mixedForm_apply,
      xlamForm_apply]
    rw [summed_mixed_value hn hN a b τ, TorsionMuDistributionNat.xValue_scale hn N a b τ]
    have hl : lambdaValue (n * N) ((n : ℤ) * a) ((n : ℤ) * b) τ = lambdaValue N a b τ := by
      unfold lambdaValue
      rw [TorsionCorrelation.reg_scale n N hn hN a b τ]
    rw [hl]
    ring
  have h := Submodule.smul_mem (classSeriesSpan (n * N) hM) (((n : ℂ) ^ 2)⁻¹) hmem
  rw [heq, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hn0), one_smul] at h
  exact h

/-! ### The second relation -/

/-- The weight-three form `x_{(u,v)} λ_{(u',v')}`. -/
def crossForm (M : ℕ) (hM : 0 < M) (u v u' v' : ℤ) : Weight M 3 :=
  lambdaTimesForm M hM u' v' (WeierstrassForms.xForm M hM u v)

theorem crossForm_apply (M : ℕ) (hM : 0 < M) (u v u' v' : ℤ) (τ : ℍ) :
    crossForm M hM u v u' v' τ = xValue M u v τ * lambdaValue M u' v' τ := by
  rw [crossForm, lambdaTimesForm_apply, WeierstrassForms.xForm_apply]
  ring

theorem lam_sum_neg (hn : 0 < n) (hN : 0 < N) (u v : ℤ) (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      lambdaValue (n * N) (u - N * ((r : ℕ) : ℤ)) (v - N * ((s : ℕ) : ℤ)) τ) =
      (n : ℂ) * lambdaValue N u v τ := by
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (n * N) := ⟨(Nat.mul_pos hn hN).ne'⟩
  have hneg : ∀ (M : ℕ) [NeZero M] (x y : ℤ), lambdaValue M (-x) (-y) τ = -lambdaValue M x y τ :=
    fun M _ x y => by unfold lambdaValue; rw [TorsionFourierComparison.reg_neg]; ring
  have he : ∀ r s : Fin n, lambdaValue (n * N) (u - N * ((r : ℕ) : ℤ)) (v - N * ((s : ℕ) : ℤ)) τ =
      -lambdaValue (n * N) (-u + N * ((r : ℕ) : ℤ)) (-v + N * ((s : ℕ) : ℤ)) τ := fun r s => by
    rw [← hneg]; congr 1 <;> ring
  simp_rw [he, Finset.sum_neg_distrib]
  rw [lam_sum hn hN, hneg]
  ring

/-- The summed mixed values along `P = A + T`, `Q = C - T`. -/
theorem summed_mixed_value_two (hn : 0 < n) (hN : 0 < N) (a b c d : ℤ) (τ : ℍ) :
    (∑ r : Fin n, ∑ s : Fin n,
      (xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ -
          xValue (n * N) ((a + N * ((r : ℕ) : ℤ)) + (c - N * ((r : ℕ) : ℤ)))
            ((b + N * ((s : ℕ) : ℤ)) + (d - N * ((s : ℕ) : ℤ))) τ) *
        (lambdaValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ +
          lambdaValue (n * N) (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) τ -
          lambdaValue (n * N) ((a + N * ((r : ℕ) : ℤ)) + (c - N * ((r : ℕ) : ℤ)))
            ((b + N * ((s : ℕ) : ℤ)) + (d - N * ((s : ℕ) : ℤ))) τ)) =
      (∑ r : Fin n, ∑ s : Fin n,
          xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ *
            lambdaValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ) +
        (∑ r : Fin n, ∑ s : Fin n,
          xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ *
            lambdaValue (n * N) (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) τ) -
        (n : ℂ) ^ 2 * xValue N a b τ * lambdaValue (n * N) (a + c) (b + d) τ -
        (n : ℂ) * xValue (n * N) (a + c) (b + d) τ * lambdaValue N a b τ -
        (n : ℂ) * xValue (n * N) (a + c) (b + d) τ * lambdaValue N c d τ +
        (n : ℂ) ^ 2 * xValue (n * N) (a + c) (b + d) τ * lambdaValue (n * N) (a + c) (b + d) τ := by
  simp_rw [show ∀ x : ℤ, (a + x) + (c - x) = a + c from fun x => by ring,
    show ∀ x : ℤ, (b + x) + (d - x) = b + d from fun x => by ring]
  set X : ℤ → ℤ → ℂ := fun u v => xValue (n * N) u v τ with hX
  set Lm : ℤ → ℤ → ℂ := fun u v => lambdaValue (n * N) u v τ with hL
  have hx := WeierstrassDistributionNat.x_distribution_nat n N hn hN τ a b
  have hla := lam_sum hn hN a b τ
  have hlc := lam_sum_neg hn hN c d τ
  change (∑ r : Fin n, ∑ s : Fin n,
      (X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) - X (a + c) (b + d)) *
        (Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
          Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) - Lm (a + c) (b + d))) =
    (∑ r : Fin n, ∑ s : Fin n, X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
        Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) +
      (∑ r : Fin n, ∑ s : Fin n, X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
        Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ))) -
      (n : ℂ) ^ 2 * xValue N a b τ * Lm (a + c) (b + d) -
      (n : ℂ) * X (a + c) (b + d) * lambdaValue N a b τ -
      (n : ℂ) * X (a + c) (b + d) * lambdaValue N c d τ +
      (n : ℂ) ^ 2 * X (a + c) (b + d) * Lm (a + c) (b + d)
  change (∑ r : Fin n, ∑ s : Fin n, X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) =
    (n : ℂ) ^ 2 * xValue N a b τ at hx
  change (∑ r : Fin n, ∑ s : Fin n, Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) =
    (n : ℂ) * lambdaValue N a b τ at hla
  change (∑ r : Fin n, ∑ s : Fin n, Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ))) =
    (n : ℂ) * lambdaValue N c d τ at hlc
  have hexp : ∀ r s : Fin n,
      (X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) - X (a + c) (b + d)) *
        (Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
          Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) - Lm (a + c) (b + d)) =
      X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) +
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) *
          Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) -
        X (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) * Lm (a + c) (b + d) -
        X (a + c) (b + d) * Lm (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) -
        X (a + c) (b + d) * Lm (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) +
        X (a + c) (b + d) * Lm (a + c) (b + d) := fun _ _ => by ring
  simp_rw [hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hx, hla, hlc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Second weight-three distribution congruence** (the relation (4.41) of the reference), with
all degenerate terms retained, for every integer label and all positive `n, N`. -/
theorem cross_distribution_mem (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b c d : ℤ) :
    (∑ r : Fin n, ∑ s : Fin n,
        crossForm (n * N) (Nat.mul_pos hn hN) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))
          (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ))) -
      (-(n : ℂ) • xlamForm (n * N) (Nat.mul_pos hn hN) ((n : ℤ) * a) ((n : ℤ) * b) +
        ((n : ℂ) ^ 2) • crossForm (n * N) (Nat.mul_pos hn hN) ((n : ℤ) * a) ((n : ℤ) * b)
          (a + c) (b + d) +
        (n : ℂ) • crossForm (n * N) (Nat.mul_pos hn hN) (a + c) (b + d) ((n : ℤ) * a) ((n : ℤ) * b) +
        (n : ℂ) • crossForm (n * N) (Nat.mul_pos hn hN) (a + c) (b + d) ((n : ℤ) * c) ((n : ℤ) * d) -
        ((n : ℂ) ^ 2) • xlamForm (n * N) (Nat.mul_pos hn hN) (a + c) (b + d)) ∈
      classSeriesSpan (n * N) (Nat.mul_pos hn hN) := by
  have hM : 0 < n * N := Nat.mul_pos hn hN
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (n * N) := ⟨hM.ne'⟩
  set S2 : Weight (n * N) 3 := ∑ r : Fin n, ∑ s : Fin n,
    mixedForm (n * N) hM (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))
      (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ)) with hS2
  have hmem2 : S2 ∈ classSeriesSpan (n * N) hM :=
    Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ => mixedForm_mem _ _ _ _ _ _
  have hmem1 := xlam_distribution_mem n N hn hN a b
  have hscale : ∀ u v : ℤ, xValue (n * N) ((n : ℤ) * u) ((n : ℤ) * v) = xValue N u v ∧
      ∀ τ : ℍ, lambdaValue (n * N) ((n : ℤ) * u) ((n : ℤ) * v) τ = lambdaValue N u v τ :=
    fun u v => ⟨funext fun τ => TorsionMuDistributionNat.xValue_scale hn N u v τ, fun τ => by
      unfold lambdaValue; rw [TorsionCorrelation.reg_scale n N hn hN u v τ]⟩
  have heq : (∑ r : Fin n, ∑ s : Fin n,
        crossForm (n * N) hM (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))
          (c - N * ((r : ℕ) : ℤ)) (d - N * ((s : ℕ) : ℤ))) -
      (-(n : ℂ) • xlamForm (n * N) hM ((n : ℤ) * a) ((n : ℤ) * b) +
        ((n : ℂ) ^ 2) • crossForm (n * N) hM ((n : ℤ) * a) ((n : ℤ) * b) (a + c) (b + d) +
        (n : ℂ) • crossForm (n * N) hM (a + c) (b + d) ((n : ℤ) * a) ((n : ℤ) * b) +
        (n : ℂ) • crossForm (n * N) hM (a + c) (b + d) ((n : ℤ) * c) ((n : ℤ) * d) -
        ((n : ℂ) ^ 2) • xlamForm (n * N) hM (a + c) (b + d)) =
      S2 - ((∑ r : Fin n, ∑ s : Fin n,
        xlamForm (n * N) hM (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ))) -
        (n : ℂ) • xlamForm (n * N) hM ((n : ℤ) * a) ((n : ℤ) * b)) := by
    apply DFunLike.ext
    intro τ
    rw [hS2]
    simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, _root_.add_apply,
      smul_eq_mul, mixedForm_apply, xlamForm_apply, crossForm_apply]
    rw [summed_mixed_value_two hn hN a b c d τ]
    simp only [(hscale a b).1, (hscale a b).2, (hscale c d).2]
    ring
  rw [heq]
  exact Submodule.sub_mem _ hmem2 hmem1

end ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeDistribution
