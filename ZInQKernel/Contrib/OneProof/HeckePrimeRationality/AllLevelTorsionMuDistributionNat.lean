import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierFinite

/-!
# Distribution relation for the quadratic torsion values `μ`

For all positive integers `n, N` and all integer labels `a, b`,
`∑_{r,s < n} μ_{nN}(a + N r, b + N s) = μ_N(a, b)`
(`mu_distribution_nat`), with the frozen zero convention.

Proof by finite arithmetic: express each `μ_{nN}` by the inverse finite Fourier duality with the
values `x_{nN}`, sum the characters over the shifts `(N r, N s)` (orthogonality at level `n`),
keep the frequencies divisible by `n`, enumerate them as `n·(A, B)` with `A, B < N`, and use
`x_{nN}(nA, nB) = x_N(A, B)`. No individual value is claimed to vanish on bad labels.
-/

noncomputable section

open Complex UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionMuDistributionNat

open TorsionWeierstrassData TorsionFourierComparison TorsionMuFourier

/-! ### Scaling of torsion data -/

theorem torsionPoint_scale {n : ℕ} (hn : 0 < n) (N : ℕ) (A B : ℤ) (τ : ℍ) :
    CompletedTheta.torsionPoint (n * N) (n * A) (n * B) τ = CompletedTheta.torsionPoint N A B τ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold CompletedTheta.torsionPoint
  push_cast
  rw [show (n : ℂ) * A * τ + n * B = n * (A * τ + B) by ring, mul_div_mul_left _ _ hn']

/-- `x_{nN}(nA, nB) = x_N(A, B)` for all integers `A, B`. -/
theorem xValue_scale {n : ℕ} (hn : 0 < n) (N : ℕ) (A B : ℤ) (τ : ℍ) :
    xValue (n * N) (n * A) (n * B) τ = xValue N A B τ := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : ∀ C : ℤ, (((n * N : ℕ) : ℤ) ∣ n * C) ↔ (N : ℤ) ∣ C := fun C => by
    push_cast; exact mul_dvd_mul_iff_left hn0
  unfold xValue
  simp only [hd, torsionPoint_scale hn]

theorem character_scale {n : ℕ} (hn : 0 < n) (N : ℕ) [NeZero N] [NeZero (n * N)]
    (A B : ℕ) (r s : ℤ) :
    character (n * N) ((n * A : ℕ) : ℤ) ((n * B : ℕ) : ℤ) r s = character N (A : ℤ) (B : ℤ) r s := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold character
  congr 1
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * B * r - n * A * s) =
      n * (2 * (Real.pi : ℂ) * Complex.I * ((B : ℂ) * r - A * s)) by ring, mul_div_mul_left _ _ hn']

/-- Splitting the character along the shifts `(N r, N s)`. -/
theorem character_split (n N : ℕ) [NeZero n] [NeZero N] [NeZero (n * N)] (A B : ℕ) (a b : ℤ)
    (r s : ℕ) :
    character (n * N) (A : ℤ) (B : ℤ) (a + N * (r : ℤ)) (b + N * (s : ℤ)) =
      character (n * N) (A : ℤ) (B : ℤ) a b * character n (s : ℤ) (r : ℤ) (B : ℤ) (A : ℤ) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-! ### Finite sums -/

theorem swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (K : γ → δ → α → β → ℂ) :
    (∑ c, ∑ d, ∑ a, ∑ b, K c d a b) = ∑ a, ∑ b, ∑ c, ∑ d, K c d a b := by
  rw [← Fintype.sum_prod_type' (fun c d => ∑ a, ∑ b, K c d a b), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Fintype.sum_prod_type' (fun c d => K c d a b)

/-- The residues below `nN` divisible by `n` are exactly `n·A'` with `A' < N`, each once. -/
theorem sum_fin_dvd (n N : ℕ) (hn : 0 < n) (f : ℕ → ℂ) :
    (∑ A : Fin (n * N), if (n : ℤ) ∣ ((A : ℕ) : ℤ) then f A else 0) =
      ∑ A' : Fin N, f (n * A') := by
  rw [Fin.sum_univ_eq_sum_range (fun A => if (n : ℤ) ∣ (A : ℤ) then f A else 0),
    Fin.sum_univ_eq_sum_range (fun A' => f (n * A')), ← Finset.sum_filter]
  have himg : (Finset.range (n * N)).filter (fun A : ℕ => (n : ℤ) ∣ (A : ℤ)) =
      (Finset.range N).image (fun A' => n * A') := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Int.natCast_dvd_natCast]
    constructor
    · rintro ⟨hA, k, rfl⟩
      exact ⟨k, Nat.lt_of_mul_lt_mul_left hA, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hk hn, dvd_mul_right n k⟩
  rw [himg, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hn h

/-! ### The distribution relation -/

/-- The summand of the inverse duality at level `L`, before the character sum. -/
def Tm (L : ℕ) [NeZero L] (a b : ℤ) (τ : ℍ) (A B : ℕ) : ℂ :=
  xValue L (A : ℤ) (B : ℤ) τ * character L (A : ℤ) (B : ℤ) a b

/-- **Distribution relation for `μ`** in every degree `n`, for all integer labels. -/
theorem mu_distribution_nat (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a b : ℤ) :
    ∑ r : Fin n, ∑ s : Fin n,
        muValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      muValue N a b τ := by
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n * N) := ⟨(Nat.mul_pos hn hN).ne'⟩
  have hμ : ∀ r s : Fin n, muValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      ∑ A : Fin (n * N), ∑ B : Fin (n * N), (-(1 / ((n * N : ℕ) : ℂ) ^ 2)) *
        (Tm (n * N) a b τ A B * character n ((s : ℕ) : ℤ) ((r : ℕ) : ℤ) ((B : ℕ) : ℤ) ((A : ℕ) : ℤ)) := by
    intro r s
    rw [mu_fourier_duality (n * N) τ]
    change -(1 / ((n * N : ℕ) : ℂ) ^ 2) * ∑ A : Fin (n * N), ∑ B : Fin (n * N),
      xValue (n * N) (A : ℕ) (B : ℕ) τ *
        character (n * N) (A : ℕ) (B : ℕ) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [character_split n N (A : ℕ) (B : ℕ) a b (r : ℕ) (s : ℕ)]
    simp only [Tm]
    ring
  have hS : ∀ A B : ℕ, (∑ r : Fin n, ∑ s : Fin n,
      character n ((s : ℕ) : ℤ) ((r : ℕ) : ℤ) (B : ℤ) (A : ℤ)) =
      if (n : ℤ) ∣ (B : ℤ) ∧ (n : ℤ) ∣ (A : ℤ) then (n : ℂ) ^ 2 else 0 := by
    intro A B
    rw [Finset.sum_comm]
    exact character_sum n (B : ℤ) (A : ℤ)
  set c : ℂ := 1 / ((n * N : ℕ) : ℂ) ^ 2 with hc
  calc ∑ r : Fin n, ∑ s : Fin n,
        muValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ
      = ∑ r : Fin n, ∑ s : Fin n, ∑ A : Fin (n * N), ∑ B : Fin (n * N), (-c) *
          (Tm (n * N) a b τ A B *
            character n ((s : ℕ) : ℤ) ((r : ℕ) : ℤ) ((B : ℕ) : ℤ) ((A : ℕ) : ℤ)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => hμ r s
    _ = ∑ A : Fin (n * N), ∑ B : Fin (n * N), ∑ r : Fin n, ∑ s : Fin n, (-c) *
          (Tm (n * N) a b τ A B *
            character n ((s : ℕ) : ℤ) ((r : ℕ) : ℤ) ((B : ℕ) : ℤ) ((A : ℕ) : ℤ)) := swap4 _
    _ = ∑ A : Fin (n * N), ∑ B : Fin (n * N), (-c) * Tm (n * N) a b τ A B *
          (if (n : ℤ) ∣ ((B : ℕ) : ℤ) ∧ (n : ℤ) ∣ ((A : ℕ) : ℤ) then (n : ℂ) ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
        rw [← hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ A : Fin (n * N), (if (n : ℤ) ∣ ((A : ℕ) : ℤ) then ∑ B : Fin (n * N),
          (if (n : ℤ) ∣ ((B : ℕ) : ℤ) then (-c) * (n : ℂ) ^ 2 * Tm (n * N) a b τ A B else 0)
          else 0) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        by_cases hA : (n : ℤ) ∣ ((A : ℕ) : ℤ)
        · simp only [hA, and_true, ↓reduceIte]
          refine Finset.sum_congr rfl fun B _ => ?_
          by_cases hB : (n : ℤ) ∣ ((B : ℕ) : ℤ)
          · simp only [hB, ↓reduceIte]; ring
          · simp only [hB, ↓reduceIte, mul_zero]
        · simp only [hA, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    _ = ∑ A' : Fin N, ∑ B' : Fin N, (-c) * (n : ℂ) ^ 2 * Tm (n * N) a b τ (n * A') (n * B') := by
        rw [sum_fin_dvd n N hn (fun A => ∑ B : Fin (n * N),
          if (n : ℤ) ∣ ((B : ℕ) : ℤ) then (-c) * (n : ℂ) ^ 2 * Tm (n * N) a b τ A B else 0)]
        refine Finset.sum_congr rfl fun A' _ => ?_
        exact sum_fin_dvd n N hn (fun B => (-c) * (n : ℂ) ^ 2 * Tm (n * N) a b τ (n * A') B)
    _ = -(1 / (N : ℂ) ^ 2) * ∑ A' : Fin N, ∑ B' : Fin N,
          xValue N ((A' : ℕ) : ℤ) ((B' : ℕ) : ℤ) τ *
            character N ((A' : ℕ) : ℤ) ((B' : ℕ) : ℤ) a b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun A' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun B' _ => ?_
        simp only [Tm]
        rw [character_scale hn N]
        have hx : xValue (n * N) ((n * (A' : ℕ) : ℕ) : ℤ) ((n * (B' : ℕ) : ℕ) : ℤ) τ =
            xValue N ((A' : ℕ) : ℤ) ((B' : ℕ) : ℤ) τ := by
          push_cast; exact xValue_scale hn N _ _ τ
        rw [hx, hc]
        have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
        push_cast
        field_simp
    _ = muValue N a b τ := by
        rw [mu_fourier_duality N τ a b]
        rfl

/-- The degree-one case is the identity. -/
example (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ) :
    ∑ r : Fin 1, ∑ s : Fin 1,
        muValue (1 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ = muValue N a b τ :=
  mu_distribution_nat 1 N one_pos hN τ a b

end ZInQ.Contrib.HeckePrimeRationality.TorsionMuDistributionNat
