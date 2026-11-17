import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationTwo

/-!
# Two-division distribution of torsion logarithmic derivatives

For a positive level `N` and integers `a, b` not both divisible by `N`, the four labels
`(a + N r, b + N s)`, `r, s ∈ {0, 1}`, are admissible at level `2N`, and
`Σ_{r,s} F_{2N}(a + N r, b + N s) = 2 F_N(a, b)`, where `F = Torsion.torsionLogDerivative`.

Proof. The completed theta function `H` satisfies the two-division multiplication identity
`∏_{r,s} H(z + (r τ + s)/2) = C exp(-2π i z) H(2z)` with `C ≠ 0`. Differentiating in `z` and
dividing by the nonzero product at `z = u = (a τ + b)/(2N)` gives
`Σ_{r,s} H'/H(u + (r τ + s)/2) = -2π i + 2 H'(2u)/H(2u)`. With the formula
`F_M(a, b) = a/M + H'(t)/(2π i H(t))` at the torsion point `t`, the completion terms contribute
`Σ_{r,s} (a + N r)/(2N) = 2a/N + 1`, and the `+1` cancels the `-2π i/(2π i)`.

No identity is assumed: the multiplication identity is the proved `H_multiplication_two`.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionTwo

open CompletedTheta

/-- The half-lattice shifts `(r τ + s)/2`. -/
def c (τ : ℍ) (r s : Fin 2) : ℂ := (((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ)) / 2

/-- Logarithmic derivative of the two-division identity. -/
theorem logDeriv_sum (τ : ℍ) (z : ℂ) (hz : ∀ r s, H τ (z + c τ r s) ≠ 0)
    (h2 : H τ (2 * z) ≠ 0) :
    Hder τ (z + c τ 0 0) / H τ (z + c τ 0 0) + Hder τ (z + c τ 0 1) / H τ (z + c τ 0 1) +
      (Hder τ (z + c τ 1 0) / H τ (z + c τ 1 0) + Hder τ (z + c τ 1 1) / H τ (z + c τ 1 1)) =
      -2 * π * I + 2 * (Hder τ (2 * z) / H τ (2 * z)) := by
  obtain ⟨C, hC, hid⟩ := H_multiplication_two τ
  set L : ℂ → ℂ := fun x =>
    (H τ (x + c τ 0 0) * H τ (x + c τ 0 1)) * (H τ (x + c τ 1 0) * H τ (x + c τ 1 1)) with hLdef
  have hLeq : ∀ x, L x = C * cexp (-2 * π * I * x) * H τ (2 * x) := by
    intro x
    have h := hid x
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two] at h
    exact h
  have hk : ∀ r s, HasDerivAt (fun x => H τ (x + c τ r s)) (Hder τ (z + c τ r s)) z :=
    fun r s => (hasDerivAt_H τ (z + c τ r s)).comp_add_const z _
  have hL : HasDerivAt L
      ((Hder τ (z + c τ 0 0) * H τ (z + c τ 0 1) + H τ (z + c τ 0 0) * Hder τ (z + c τ 0 1)) *
          (H τ (z + c τ 1 0) * H τ (z + c τ 1 1)) +
        (H τ (z + c τ 0 0) * H τ (z + c τ 0 1)) *
          (Hder τ (z + c τ 1 0) * H τ (z + c τ 1 1) + H τ (z + c τ 1 0) * Hder τ (z + c τ 1 1)))
      z :=
    ((hk 0 0).mul (hk 0 1)).mul ((hk 1 0).mul (hk 1 1))
  have he : HasDerivAt (fun x : ℂ => cexp (-2 * π * I * x)) (cexp (-2 * π * I * z) * (-2 * π * I))
      z := by
    simpa using ((hasDerivAt_id z).const_mul (-2 * π * I : ℂ)).cexp
  have hd2 : HasDerivAt (fun x : ℂ => H τ (2 * x)) (Hder τ (2 * z) * 2) z := by
    have h := (hasDerivAt_H τ (2 * z)).comp z ((hasDerivAt_id' z).const_mul (2 : ℂ))
    exact h.congr_deriv (by ring)
  have hR := (he.const_mul C).mul hd2
  have hR' : HasDerivAt L
      (C * (cexp (-2 * π * I * z) * (-2 * π * I)) * H τ (2 * z) +
        C * cexp (-2 * π * I * z) * (Hder τ (2 * z) * 2)) z := by
    have hfun : L = fun x => C * cexp (-2 * π * I * x) * H τ (2 * x) := funext hLeq
    rw [hfun]
    exact hR
  have hderiv := hL.unique hR'
  have hval := hLeq z
  simp only [hLdef] at hval
  have h00 := hz 0 0
  have h01 := hz 0 1
  have h10 := hz 1 0
  have h11 := hz 1 1
  have hE := Complex.exp_ne_zero (-2 * π * I * z)
  generalize H τ (z + c τ 0 0) = A00 at *
  generalize H τ (z + c τ 0 1) = A01 at *
  generalize H τ (z + c τ 1 0) = A10 at *
  generalize H τ (z + c τ 1 1) = A11 at *
  generalize Hder τ (z + c τ 0 0) = D00 at *
  generalize Hder τ (z + c τ 0 1) = D01 at *
  generalize Hder τ (z + c τ 1 0) = D10 at *
  generalize Hder τ (z + c τ 1 1) = D11 at *
  generalize H τ (2 * z) = h at *
  generalize Hder τ (2 * z) = h' at *
  generalize cexp (-2 * π * I * z) = E at *
  field_simp
  linear_combination h * hderiv - (-2 * π * I * h + 2 * h') * hval

/-- Admissibility of the four preimages at level `2N`. -/
theorem good_preimage {N : ℕ} {a b : ℤ} (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (r s : Fin 2) :
    ¬ (((2 * N : ℕ) : ℤ) ∣ a + N * ((r : ℕ) : ℤ) ∧ ((2 * N : ℕ) : ℤ) ∣ b + N * ((s : ℕ) : ℤ)) := by
  rintro ⟨h1, h2⟩
  apply hg
  have hd : (N : ℤ) ∣ ((2 * N : ℕ) : ℤ) := ⟨2, by push_cast; ring⟩
  exact ⟨(dvd_add_left (dvd_mul_right _ _)).mp (hd.trans h1),
    (dvd_add_left (dvd_mul_right _ _)).mp (hd.trans h2)⟩

theorem torsionPoint_preimage (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) (r s : Fin 2) :
    torsionPoint (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      torsionPoint N a b τ / 2 + c τ r s := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold torsionPoint c
  push_cast
  field_simp
  ring

theorem termF (N : ℕ) (hN : 0 < N) (a b : ℤ) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ)
    (r s : Fin 2) :
    Torsion.torsionLogDerivative (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      ((a + N * ((r : ℕ) : ℤ) : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ) +
        Hder τ (torsionPoint N a b τ / 2 + c τ r s) /
          (2 * π * I * H τ (torsionPoint N a b τ / 2 + c τ r s)) := by
  rw [torsionLogDerivative_eq (2 * N) (by omega) τ _ _ (good_preimage hg r s),
    torsionPoint_preimage N hN a b τ r s]

/-- **Two-division distribution for admissible labels.** -/
theorem distribution_two (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∑ r : Fin 2, ∑ s : Fin 2,
        Torsion.torsionLogDerivative (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      2 * Torsion.torsionLogDerivative N a b τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set t := torsionPoint N a b τ with ht
  set u := t / 2 with hu
  have h2u : 2 * u = t := by rw [hu]; ring
  have hz : ∀ r s, H τ (u + c τ r s) ≠ 0 := by
    intro r s
    rw [hu, ← torsionPoint_preimage N hN a b τ r s]
    exact H_torsion_ne_zero (2 * N) (by omega) τ _ _ (good_preimage hg r s)
  have ht0 : H τ t ≠ 0 := H_torsion_ne_zero N hN τ a b hg
  have hls := logDeriv_sum τ u hz (by rw [h2u]; exact ht0)
  rw [h2u] at hls
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, termF N hN a b hg τ,
    termF N hN a b hg τ, termF N hN a b hg τ, termF N hN a b hg τ,
    torsionLogDerivative_eq N hN τ a b hg, ← ht]
  rw [← hu]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero,
    mul_one]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h00 := hz 0 0
  have h01 := hz 0 1
  have h10 := hz 1 0
  have h11 := hz 1 1
  generalize H τ (u + c τ 0 0) = A00 at *
  generalize H τ (u + c τ 0 1) = A01 at *
  generalize H τ (u + c τ 1 0) = A10 at *
  generalize H τ (u + c τ 1 1) = A11 at *
  generalize Hder τ (u + c τ 0 0) = D00 at *
  generalize Hder τ (u + c τ 0 1) = D01 at *
  generalize Hder τ (u + c τ 1 0) = D10 at *
  generalize Hder τ (u + c τ 1 1) = D11 at *
  generalize H τ t = h at *
  generalize Hder τ t = h' at *
  have key : D00 / A00 + D01 / A01 + (D10 / A10 + D11 / A11) =
      -2 * π * I + 2 * (h' / h) := hls
  have e1 : D00 / (2 * π * I * A00) + D01 / (2 * π * I * A01) +
      (D10 / (2 * π * I * A10) + D11 / (2 * π * I * A11)) =
      (D00 / A00 + D01 / A01 + (D10 / A10 + D11 / A11)) / (2 * π * I) := by
    field_simp
  push_cast
  have e2 : (a : ℂ) / (2 * N) + D00 / (2 * π * I * A00) + ((a : ℂ) / (2 * N) +
      D01 / (2 * π * I * A01)) + (((a : ℂ) + N) / (2 * N) + D10 / (2 * π * I * A10) +
      (((a : ℂ) + N) / (2 * N) + D11 / (2 * π * I * A11))) =
      (2 * a / N + 1) + (D00 / (2 * π * I * A00) + D01 / (2 * π * I * A01) +
      (D10 / (2 * π * I * A10) + D11 / (2 * π * I * A11))) := by
    field_simp
    ring
  rw [e2, e1, key]
  field_simp
  ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionTwo
