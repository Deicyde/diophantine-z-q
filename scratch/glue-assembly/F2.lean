import Mathlib

/-!
# Step F2 of h-trust: `h(Φ(z)) ≤ 40 h(z) + 22` over Mathlib's Weil heights

`Φ(z) = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` (N5 L920-932). The statement is about Mathlib's genuine
Weil height `Height.logHeight` on a field with admissible absolute values (number fields).
-/

namespace GlueAssembly

open MvPolynomial Height Real

/-- The two coordinates of `Φ`, as polynomials over `ℕ` in ten variables. -/
noncomputable def PhiNat : Fin 2 → MvPolynomial (Fin 10) ℕ :=
  ![C 3779136 * (∏ i, X i) ^ 4, (∑ i, X i ^ 8) ^ 5]

theorem PhiNat_homogeneous (j : Fin 2) : (PhiNat j).IsHomogeneous 40 := by
  fin_cases j
  · have h1 : (∏ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ)).IsHomogeneous 10 := by
      have := IsHomogeneous.prod (Finset.univ : Finset (Fin 10)) (fun i => (X i : MvPolynomial (Fin 10) ℕ))
        (fun _ => 1) (fun i _ => isHomogeneous_X ℕ i)
      simpa using this
    have := (h1.pow 4).C_mul 3779136
    simpa [PhiNat] using this
  · have h1 : (∑ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ) ^ 8).IsHomogeneous 8 :=
      IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 8)
    simpa [PhiNat] using h1.pow 5

/-- The sum of the coefficients of a polynomial over `ℕ` is its value at `1`. -/
theorem sum_coeff_eq_eval_one {σ : Type*} (P : MvPolynomial σ ℕ) :
    ∑ s ∈ P.support, P.coeff s = eval (fun _ => 1) P := by
  rw [eval_eq]; simp

theorem PhiNat_eval_one (j : Fin 2) : eval (fun _ => 1) (PhiNat j) ≤ 3779136 := by
  fin_cases j <;> simp [PhiNat]

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- `Φ`'s coordinates over `K`. -/
noncomputable def PhiK (K : Type*) [CommSemiring K] : Fin 2 → MvPolynomial (Fin 10) K :=
  fun j => map (Nat.castRingHom K) (PhiNat j)

theorem PhiK_eval (z : Fin 10 → K) :
    (fun j => (PhiK K j).eval z) = ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] := by
  ext j; fin_cases j <;> simp [PhiK, PhiNat]

/-- Local bound at an absolute value: the `ℓ¹`-norm of the coefficients is at most the value at
`1` of the `ℕ`-polynomial. -/
theorem coeff_sum_le (v : AbsoluteValue K ℝ) (P : MvPolynomial (Fin 10) ℕ) :
    (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) ≤
      ((eval (fun _ => 1) P : ℕ) : ℝ) := by
  have e : (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) =
      ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s) := rfl
  rw [e, ← sum_coeff_eq_eval_one]
  push_cast
  calc ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s)
      ≤ ∑ s ∈ P.support, v ((map (Nat.castRingHom K) P).coeff s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (support_map_subset _ _)
          (fun _ _ _ => v.nonneg _)
    _ ≤ ∑ s ∈ P.support, (P.coeff s : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [coeff_map]
        simpa using v.apply_nat_le_self (P.coeff s)

theorem mulHeightBound_PhiK_le :
    mulHeightBound (PhiK K) ≤ (3779136 : ℝ) ^ totalWeight K := by
  rw [mulHeightBound_eq]
  have hnon : (∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal (K := K),
      ⨆ j, max (⨆ s : (PhiK K j).support, v.val ((PhiK K j).coeff s)) 1) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv := AdmissibleAbsValues.isNonarchimedean v.val v.prop
    refine le_antisymm (ciSup_le fun j => max_le ?_ le_rfl) ?_
    · rcases isEmpty_or_nonempty (PhiK K j).support with h | h
      · simp
      refine ciSup_le fun s => ?_
      simp only [PhiK, coeff_map]
      exact hv.apply_natCast_le_one (map_zero_le v.val 1) (map_one v.val)
    · exact le_trans (le_max_right _ 1) (Finite.le_ciSup_of_le (0 : Fin 2) le_rfl)
  rw [hnon, mul_one]
  have hle : ∀ v ∈ AdmissibleAbsValues.archAbsVal (K := K),
      (⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)) ≤ (3779136 : ℝ) := by
    intro v _
    refine ciSup_le fun j => (coeff_sum_le v (PhiNat j)).trans ?_
    exact_mod_cast PhiNat_eval_one j
  calc (AdmissibleAbsValues.archAbsVal.map fun v =>
        ⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)).prod
      ≤ (AdmissibleAbsValues.archAbsVal.map fun _ => (3779136 : ℝ)).prod :=
        Multiset.prod_map_le_prod_map₀ _ _
          (fun v _ => Real.iSup_nonneg fun j => Finsupp.sum_nonneg' fun _ => v.nonneg _) hle
    _ = (3779136 : ℝ) ^ totalWeight K := by
        simp [totalWeight]

/-- **F2, relative form.** For `z ∈ K¹⁰` (any field with admissible absolute values), the
projective height of `[3779136 (∏ z_m)⁴ : (∑ z_m⁸)⁵]` is at most
`40 h_K(z) + n_K log 3779136`, `n_K` the total weight (`= [K:ℚ]` for number fields). -/
theorem logHeight_Phi_le (z : Fin 10 → K) :
    logHeight ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  have hp : ∀ j, (PhiK K j).IsHomogeneous 40 := fun j => (PhiNat_homogeneous j).map _
  have h := logHeight_eval_le hp z
  rw [PhiK_eval] at h
  have hB : log (max (mulHeightBound (PhiK K)) 1) ≤ totalWeight K * log 3779136 := by
    rw [← Real.log_pow]
    refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) ?_
    exact max_le mulHeightBound_PhiK_le (one_le_pow₀ (by norm_num))
  push_cast at h
  linarith

/-- **F2, affine form**: `h_K(Φ(z)) ≤ 40 h_K(z) + n_K log 3779136`, with `Φ(z)` the quotient. -/
theorem logHeight₁_Phi_le (z : Fin 10 → K) :
    logHeight₁ (3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5) ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  rw [logHeight₁_div_eq_logHeight]; exact logHeight_Phi_le z

end GlueAssembly
