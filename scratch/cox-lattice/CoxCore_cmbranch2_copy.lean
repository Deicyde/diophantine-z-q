import Mathlib

/-! cm-branch2 scratch: the discriminant of an order `ℤ[θ]` of a quadratic field. -/

open NumberField Module

namespace CoxCore

variable {k : Type} [Field k] [NumberField k]

/-- The trace discriminant of `(1, θ)` for `θ² + bθ + N = 0`, `θ ∉ ℚ`, `[k:ℚ] = 2`. -/
theorem discr_pair (hk : finrank ℚ k = 2) {θ : k} (hnq : θ ∉ Set.range (algebraMap ℚ k)) {b N : ℤ}
    (hθ : θ ^ 2 + b * θ + N = 0) (hli : LinearIndependent ℚ ![(1 : k), θ]) :
    Algebra.discr ℚ ![(1 : k), θ] = (b : ℚ) ^ 2 - 4 * N := by
  classical
  let B : Basis (Fin 2) ℚ k := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hk])
  have hB : ∀ i, B i = ![(1 : k), θ] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hB0 : B 0 = 1 := hB 0
  have hB1 : B 1 = θ := hB 1
  have hθ2 : θ * θ = (-(N : ℚ)) • B 0 + (-(b : ℚ)) • B 1 := by
    rw [hB0, hB1, Algebra.smul_def, Algebra.smul_def]
    simp only [map_neg, map_intCast, mul_one]
    linear_combination hθ
  have htr : ∀ x : k, Algebra.trace ℚ k x = (Algebra.leftMulMatrix B x).trace :=
    fun x => Algebra.trace_eq_matrix_trace B x
  have hrep : ∀ x : k, ∀ i j, Algebra.leftMulMatrix B x i j = B.repr (x * B j) i :=
    fun x i j => Algebra.leftMulMatrix_eq_repr_mul B x i j
  have t1 : Algebra.trace ℚ k 1 = 2 := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, one_mul, one_mul, B.repr_self, B.repr_self]
    simp; norm_num
  have tθ : Algebra.trace ℚ k θ = -b := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, hB0, mul_one, ← hB1, B.repr_self, hB1, hθ2]
    simp [Finsupp.single_apply]
  have tθθ : Algebra.trace ℚ k (θ * θ) = b ^ 2 - 2 * N := by
    rw [hθ2, map_add, map_smul, map_smul, hB0, hB1, t1, tθ]
    simp; ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, one_mul]
  rw [t1, tθ, tθθ]
  ring

/-- `𝓞_k` as the additive closure of an integral basis. -/
theorem ringOfIntegers_eq_closure {ι : Type} [Fintype ι] (e : Free.ChooseBasisIndex ℤ (𝓞 k) ≃ ι) :
    (integralClosure ℤ k).toSubring.toAddSubgroup =
      AddSubgroup.closure (Set.range ((integralBasis k).reindex e)) := by
  rw [Basis.range_reindex]
  apply le_antisymm
  · intro x hx
    let y : 𝓞 k := ⟨x, hx⟩
    have hy := (RingOfIntegers.basis k).sum_repr y
    have hx' : x = ∑ i, ((RingOfIntegers.basis k).repr y i) • integralBasis k i := by
      have := congrArg (algebraMap (𝓞 k) k) hy
      simp only [map_sum, map_zsmul] at this
      simp only [integralBasis_apply]
      rw [this]
      rfl
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact (RingOfIntegers.basis k i).2

/-- **The discriminant of `ℤ[θ]`**: for `R = ℤ + ℤθ ⊆ 𝓞_k`, `θ² + bθ + N = 0`, `[k:ℚ] = 2`,
`b² − 4N = [𝓞_k : R]² · d_k`. -/
theorem discr_order (hk : finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    {θ : k} (hθR : θ ∈ R) (hgen : ∀ r ∈ R, ∃ m n : ℤ, r = m + n * θ)
    (hnq : θ ∉ Set.range (algebraMap ℚ k)) (hli : LinearIndependent ℚ ![(1 : k), θ]) {b N : ℤ}
    (hθ : θ ^ 2 + b * θ + N = 0) :
    b ^ 2 - 4 * N =
      (R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup : ℤ) ^ 2 * discr k := by
  classical
  let B₁ : Basis (Fin 2) ℚ k := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hk])
  have hB₁ : ⇑B₁ = ![(1 : k), θ] := by
    funext i; simp [B₁, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 k)) = Fintype.card (Fin 2) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hk, Fintype.card_fin]
  let e := Fintype.equivOfCardEq hcard
  let B₂ : Basis (Fin 2) ℚ k := (integralBasis k).reindex e
  have h₁ : R.toAddSubgroup = AddSubgroup.closure (Set.range B₁) := by
    rw [hB₁]
    apply le_antisymm
    · intro r hr
      obtain ⟨m, n, rfl⟩ := hgen r hr
      refine AddSubgroup.add_mem _ ?_ ?_
      · have : ((m : ℤ) : k) = m • (1 : k) := by simp
        rw [this]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (0 : Fin 2))) _
      · have : (n : k) * θ = n • θ := by simp [zsmul_eq_mul]
        rw [this]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 2))) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact R.one_mem
      · exact hθR
  have h₂ := ringOfIntegers_eq_closure (k := k) e
  have hidx := AddSubgroup.relIndex_eq_abs_det R.toAddSubgroup
    (integralClosure ℤ k).toSubring.toAddSubgroup hR B₁ B₂ h₁ h₂
  have hdisc : Algebra.discr ℚ ⇑B₁ = (B₂.det B₁) ^ 2 * Algebra.discr ℚ ⇑B₂ := by
    conv_lhs => rw [← B₂.toMatrix_map_vecMul B₁]
    rw [Algebra.discr_of_matrix_vecMul, Basis.det_apply]
  have hB₂ : Algebra.discr ℚ ⇑B₂ = discr k := by
    rw [coe_discr]
    have := Algebra.discr_reindex ℚ (integralBasis k) e
    rw [← this]
    simp [B₂, Basis.coe_reindex]
  have hp := discr_pair hk hnq hθ hli
  rw [← hB₁] at hp
  have key : ((b ^ 2 - 4 * N : ℤ) : ℚ) =
      ((R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup : ℤ) ^ 2 * discr k : ℤ) := by
    push_cast
    rw [← hp, hdisc, hB₂, ← sq_abs (B₂.det B₁), ← hidx]
  exact_mod_cast key

end CoxCore
