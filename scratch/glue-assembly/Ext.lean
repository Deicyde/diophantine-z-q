import Mathlib

/-!
# Height of a rational number in a number field

`h_K(q) = [K:ℚ] · log max(|num q|, den q)` for `q ∈ ℚ` and a number field `K` (Mathlib's relative
height `Height.logHeight₁`). This is the invariance of the absolute height under finite
extension, for rational numbers.
-/

namespace GlueAssembly

open Height NumberField Real

variable {K : Type*} [Field K] [NumberField K]

theorem iSup_fin_two (f : Fin 2 → ℝ) : ⨆ i, f i = max (f 0) (f 1) := by
  refine le_antisymm (ciSup_le fun i => ?_) (max_le (Finite.le_ciSup_of_le 0 le_rfl)
    (Finite.le_ciSup_of_le 1 le_rfl))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- At a finite place, a coprime pair of integers has maximal absolute value `1`. -/
theorem finitePlace_max_eq_one (v : FinitePlace K) {a b : ℤ} (hab : IsCoprime a b) :
    max (v (a : K)) (v (b : K)) = 1 := by
  have hv : IsNonarchimedean (v : K → ℝ) := FinitePlace.add_le v
  have H (n : ℤ) : v (n : K) ≤ 1 :=
    hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  obtain ⟨s, t, hst⟩ := hab
  refine le_antisymm (max_le (H a) (H b)) ?_
  have h1 : (1 : ℝ) = v ((s : K) * a + (t : K) * b) := by
    have : ((s : K) * a + (t : K) * b) = ((s * a + t * b : ℤ) : K) := by push_cast; ring
    rw [this, hst]; simp
  rw [h1]
  refine (hv _ _).trans (max_le_max ?_ ?_)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H s)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H t)

/-- The multiplicative height over `K` of a coprime integer pair `[a : b]` is
`max(|a|, |b|)^[K:ℚ]`. -/
theorem mulHeight_intPair {a b : ℤ} (hab : IsCoprime a b) (hb : b ≠ 0) :
    mulHeight ![(a : K), (b : K)] = (max |(a : ℝ)| |(b : ℝ)|) ^ Module.finrank ℚ K := by
  have hx : ![(a : K), (b : K)] ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
    exact hb this
  rw [NumberField.mulHeight_eq hx]
  have hfin : (∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), (b : K)] i)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [iSup_fin_two]
    simpa using finitePlace_max_eq_one v hab
  rw [hfin, mul_one]
  have hinf : ∀ v : InfinitePlace K, (⨆ i, v (![(a : K), (b : K)] i)) = max |(a : ℝ)| |(b : ℝ)| := by
    intro v
    rw [iSup_fin_two]
    simp [InfinitePlace.map_intCast, Int.norm_eq_abs]
  simp_rw [hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

/-- **Height of a rational number in a number field.** `h_K(q) = [K:ℚ] · log max(|num|, den)`. -/
theorem logHeight₁_algebraMap_rat (q : ℚ) :
    logHeight₁ (algebraMap ℚ K q) =
      Module.finrank ℚ K * log (max |(q.num : ℝ)| (q.den : ℝ)) := by
  have hden : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : algebraMap ℚ K q = ((q.num : ℤ) : K) / ((q.den : ℤ) : K) := by
    conv_lhs => rw [← Rat.num_div_den q]
    simp
  rw [e, logHeight₁_div_eq_logHeight, logHeight_eq_log_mulHeight,
    mulHeight_intPair (Rat.isCoprime_num_den q) (by exact_mod_cast q.den_nz), Real.log_pow]
  congr 2
  push_cast
  rw [abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℝ) < q.den)]

end GlueAssembly
