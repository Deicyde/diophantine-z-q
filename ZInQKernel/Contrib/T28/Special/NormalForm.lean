import ZInQKernel.Contrib.T28.Special.Bolza

/-!
# T28, special locus: every sextic with `J₁₀ ≠ 0` is equivalent to a root normal form
(task igusa-special)

Over an algebraically closed field of characteristic `0`, a binary sextic `f` with `J₁₀ f ≠ 0`
is `GL₂ × 𝔾_m`-equivalent to `Nr l m n = x(x-1)(x-l)(x-m)(x-n)` (`exists_Nr`): move a root to
`∞`, a second root to `0`, a third to `1` and normalize the leading coefficient; `J₁₀ ≠ 0`
excludes double roots at `∞` and `0` (`J10_zero_56`, `J10_zero_01`).
No `sorry`, no `axiom`.
-/

namespace T28Special
open PkgI1 Polynomial

section Roots
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem root6 (a0 a1 a2 a3 a4 a5 : K) :
    ∃ x : K, x ^ 6 + a5 * x ^ 5 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 :
      K[X]).degree = 6 := by compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X])
    (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

theorem root5 (a0 a1 a2 a3 a4 : K) :
    ∃ x : K, x ^ 5 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 :
      K[X]).degree = 5 := by compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X])
    (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

theorem root4 (a0 a1 a2 a3 : K) :
    ∃ x : K, x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X]).degree = 4 := by
    compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X]) (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

theorem root3 (a0 a1 a2 : K) : ∃ x : K, x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X]).degree = 3 := by compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : K[X])
    (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

theorem root2 (a0 a1 : K) : ∃ x : K, x ^ 2 + a1 * x + a0 = 0 := by
  have hd : (X ^ 2 + C a1 * X + C a0 : K[X]).degree = 2 := by compute_degree!
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 2 + C a1 * X + C a0 : K[X])
    (by rw [hd]; decide)
  exact ⟨x, by simpa using hx⟩

/-- A monic cubic splits. -/
theorem cubic_split (e1 e2 e3 : K) :
    ∃ l m n : K, l + m + n = e1 ∧ l * m + l * n + m * n = e2 ∧ l * m * n = e3 := by
  obtain ⟨l, hl⟩ := root3 (-e3) e2 (-e1)
  obtain ⟨m, hm⟩ := root2 (e2 + l * (l - e1)) (l - e1)
  refine ⟨l, m, -(l - e1) - m, by ring, by linear_combination -hm, ?_⟩
  linear_combination (-l) * hm + hl

end Roots

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Step 1: a root at `∞`. -/
theorem step_inf (f : Fin 7 → K) : ∃ g, Eqv f g ∧ g 6 = 0 := by
  by_cases h6 : f 6 = 0
  · exact ⟨f, Eqv.refl f, h6⟩
  obtain ⟨x, hx⟩ := root6 (f 0 / f 6) (f 1 / f 6) (f 2 / f 6) (f 3 / f 6) (f 4 / f 6) (f 5 / f 6)
  refine ⟨actC f x 1 1 0 1, Eqv.of_actC _ _ _ _ _ _ (by norm_num) one_ne_zero, ?_⟩
  have e1 : actC f x 1 1 0 1 6 = f 6 * (x ^ 6 + f 5 / f 6 * x ^ 5 + f 4 / f 6 * x ^ 4 +
      f 3 / f 6 * x ^ 3 + f 2 / f 6 * x ^ 2 + f 1 / f 6 * x + f 0 / f 6) := by
    simp [actC]; field_simp; ring
  rw [e1, hx, mul_zero]

/-- Step 2: a second root at `0`. -/
theorem step_zero (g : Fin 7 → K) (hJ : J10 g ≠ 0) (h6 : g 6 = 0) :
    ∃ h, Eqv g h ∧ h 6 = 0 ∧ h 0 = 0 := by
  have h5 : g 5 ≠ 0 := fun h => hJ (J10_zero_56 g h h6)
  obtain ⟨x, hx⟩ := root5 (g 0 / g 5) (g 1 / g 5) (g 2 / g 5) (g 3 / g 5) (g 4 / g 5)
  refine ⟨actC g 1 x 0 1 1, Eqv.of_actC _ _ _ _ _ _ (by norm_num) one_ne_zero, ?_, ?_⟩
  · simp [actC, h6]
  · have e1 : actC g 1 x 0 1 1 0 = g 5 * (x ^ 5 + g 4 / g 5 * x ^ 4 + g 3 / g 5 * x ^ 3 +
        g 2 / g 5 * x ^ 2 + g 1 / g 5 * x + g 0 / g 5) := by
      simp [actC, h6]; field_simp; ring
    rw [e1, hx, mul_zero]

/-- Step 3: a third root at `1`, leading coefficient `1`. -/
theorem step_one (h : Fin 7 → K) (hJ : J10 h ≠ 0) (h6 : h 6 = 0) (h0 : h 0 = 0) :
    ∃ e1 e2 e3 : K, Eqv h (Ne e1 e2 e3) := by
  have h5 : h 5 ≠ 0 := fun h' => hJ (J10_zero_56 h h' h6)
  have h1 : h 1 ≠ 0 := fun h' => hJ (J10_zero_01 h h0 h')
  obtain ⟨t, ht⟩ := root4 (h 1 / h 5) (h 2 / h 5) (h 3 / h 5) (h 4 / h 5)
  have ht0 : t ≠ 0 := by
    rintro rfl; apply h1
    have : h 1 / h 5 = 0 := by simpa using ht
    simpa [h5] using this
  have hsum : h 1 * t + h 2 * t ^ 2 + h 3 * t ^ 3 + h 4 * t ^ 4 + h 5 * t ^ 5 = 0 := by
    have : h 5 * t * (t ^ 4 + h 4 / h 5 * t ^ 3 + h 3 / h 5 * t ^ 2 + h 2 / h 5 * t + h 1 / h 5) =
        h 1 * t + h 2 * t ^ 2 + h 3 * t ^ 3 + h 4 * t ^ 4 + h 5 * t ^ 5 := by field_simp; ring
    rw [← this, ht, mul_zero]
  set c := 1 / (h 5 * t ^ 5) with hc
  have hc5 : h 5 * t ^ 5 * c = 1 := by rw [hc]; field_simp
  refine ⟨-(1 + h 4 * t ^ 4 * c), h 3 * t ^ 3 * c + 1 + h 4 * t ^ 4 * c, h 1 * t * c,
    (Eqv.of_actC h t 0 0 1 c (by simpa using ht0) (by simp [hc, h5, ht0])).of_eq ?_⟩
  funext i
  fin_cases i <;> simp [actC, Ne, h0, h6, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | ring1 | linear_combination c * hsum - hc5 | linear_combination hc5

/-- **Root normal form**: every sextic with `J₁₀ ≠ 0` is equivalent to some
`x(x-1)(x-l)(x-m)(x-n)`. -/
theorem exists_Nr (f : Fin 7 → K) (hf : J10 f ≠ 0) : ∃ l m n : K, Eqv f (Nr l m n) := by
  obtain ⟨g, hfg, hg6⟩ := step_inf f
  have hg := hfg.J10_ne_zero hf
  obtain ⟨h, hgh, hh6, hh0⟩ := step_zero g hg hg6
  obtain ⟨e1, e2, e3, hN⟩ := step_one h (hgh.J10_ne_zero hg) hh6 hh0
  obtain ⟨l, m, n, h1, h2, h3⟩ := cubic_split (K := K) e1 e2 e3
  refine ⟨l, m, n, (hfg.trans hgh).trans (hN.of_eq ?_)⟩
  rw [Nr, h1, h2, h3]

end T28Special
