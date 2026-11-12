import Mathlib

/-!
# Elementary glue of step F3: normalizations of the theta height (N5 L934-947)

* `mulHeight_le_mulHeightL2`: the projective height with the Euclidean (`L²`) norm at the
  archimedean places dominates Mathlib's sup-norm height (N5: "His Euclidean projective height
  dominates our supremum projective height").
* `logHeight_sixteen_eq`: adjoining the six vanishing odd theta constants does not change the
  height (N5 L932-933), Mathlib's `logHeight_sumElim_zero_eq`.
* `logHeight_rootsOfUnity_smul`: multiplying coordinates by roots of unity does not change the
  height (N5 L937: the permitted changes of theta structure permute coordinates and multiply them
  by roots of unity).
-/

namespace GlueAssembly

open Height Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

/-- The multiplicative projective height with the `L²` norm at the archimedean places and the
max norm at the nonarchimedean ones (relative to `K`; junk value `1` at `0`). -/
noncomputable def mulHeightL2 (x : ι → K) : ℝ :=
  open Classical in
  if x = 0 then 1 else
    (AdmissibleAbsValues.archAbsVal.map fun v => √(∑ i, v (x i) ^ 2)).prod *
      ∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal, ⨆ i, v.val (x i)

/-- The `L²` projective height dominates the sup-norm one. -/
theorem mulHeight_le_mulHeightL2 (x : ι → K) : mulHeight x ≤ mulHeightL2 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [mulHeightL2]
  rw [mulHeight_eq hx, mulHeightL2, if_neg hx]
  refine mul_le_mul_of_nonneg_right ?_
    (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass _ _)
  refine Multiset.prod_map_le_prod_map₀ _ _
    (fun v _ => Real.iSup_nonneg_of_nonnegHomClass _ _) fun v _ => ?_
  have : Nonempty ι := by
    obtain ⟨i, _⟩ := Function.ne_iff.mp hx
    exact ⟨i⟩
  refine ciSup_le fun i => Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => v (x j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- Logarithmic form. -/
theorem logHeight_le_log_mulHeightL2 (x : ι → K) : logHeight x ≤ log (mulHeightL2 x) :=
  log_le_log (mulHeight_pos x) (mulHeight_le_mulHeightL2 x)

/-- The ten even theta constants and the sixteen (six odd ones vanish) have the same height. -/
theorem logHeight_sixteen_eq (z : Fin 10 → K) :
    logHeight (Sum.elim z (0 : Fin 6 → K)) = logHeight z :=
  logHeight_sumElim_zero_eq z

/-- Multiplying the coordinates by roots of unity does not change the height: for `ζ i ^ n = 1`
(`n ≥ 1`), `mulHeight (ζ * x) = mulHeight x`. -/
theorem mulHeight_rootsOfUnity_mul {n : ℕ} (hn : 0 < n) (ζ x : ι → K) (hζ : ∀ i, ζ i ^ n = 1) :
    mulHeight (ζ * x) = mulHeight x := by
  have hv : ∀ v : AbsoluteValue K ℝ, ∀ i, v (ζ i) = 1 := by
    intro v i
    have h := congrArg v (hζ i)
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (v.nonneg _) hn.ne').1 h
  have hz : ∀ i, ζ i ≠ 0 := fun i h => by simpa [h, zero_pow hn.ne'] using hζ i
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : ζ * x ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Function.ne_iff.mpr ⟨i, by simpa using mul_ne_zero (hz i) hi⟩
  rw [mulHeight_eq hx, mulHeight_eq hx']
  simp only [Pi.mul_apply, map_mul, hv, one_mul]

end GlueAssembly
