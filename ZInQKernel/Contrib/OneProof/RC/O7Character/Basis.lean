import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.SqrtDiscr
import ZInQKernel.Progressions.QuadField.Discriminant

/-! The integral basis used in the optimal embedding test, tex 9121–9131. -/

noncomputable section

open scoped NumberField
open NumberField Matrix
open ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Progressions

namespace ZInQ.Manuscript.RC.O7Character

open O7Actual

variable {F : Type} [Field F] [NumberField F] {d : ℤ}

private theorem half_discr :
    Algebra.discr ℚ (![1, (1 / 2 : ℚ) • (1 + QuadraticAlgebra.omega)] : Fin 2 → Qsqrt d) =
      (d : ℚ) := by
  let P : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1 / 2; 0, 1 / 2]
  have hP : P.det = 1 / 2 := by norm_num [P, Matrix.det_fin_two]
  have hv : (![1, (1 / 2 : ℚ) • (1 + QuadraticAlgebra.omega)] : Fin 2 → Qsqrt d) =
      Matrix.vecMul (⇑(QuadraticAlgebra.basis (d : ℚ) 0))
        (P.map (algebraMap ℚ (Qsqrt d))) := by
    funext i
    fin_cases i
    · simp [P, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · simp [P, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Algebra.smul_def]
      ring
  rw [hv, Algebra.discr_of_matrix_vecMul, hP, Qsqrt.discr_basis]
  ring

private theorem spans_of_discr (h₂ : Module.finrank ℚ F = 2) (x : Fin 2 → 𝓞 F)
    (hx : Algebra.discr ℚ (fun i => (x i : F)) = (discr F : ℚ)) (y : 𝓞 F) :
    ∃ a : Fin 2 → ℤ, y = ∑ i, a i • x i := by
  classical
  let b := RingOfIntegers.basis F
  let bQ := integralBasis F
  let e := Fintype.equivFinOfCardEq
    (show Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = 2 by
      rw [← Module.finrank_eq_card_basis bQ, h₂])
  let c := b.reindex e
  let cQ := bQ.reindex e
  let P : Matrix (Fin 2) (Fin 2) ℤ := c.toMatrix x
  have hP : cQ.toMatrix (fun i => (x i : F)) = P.map (Int.castRingHom ℚ) := by
    ext i j
    simp only [cQ, c, P, Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply]
    exact integralBasis_repr_apply F (x j) (e.symm i)
  have hdet : (P.det : ℚ) ^ 2 * (discr F : ℚ) = (discr F : ℚ) := calc
    _ = (cQ.toMatrix (fun i => (x i : F))).det ^ 2 * Algebra.discr ℚ cQ := by
      have hm : (P.map (Int.castRingHom ℚ)).det = (P.det : ℚ) :=
        (RingHom.map_det (Int.castRingHom ℚ) P).symm
      rw [hP, hm, Module.Basis.coe_reindex, Algebra.discr_reindex, ← coe_discr]
    _ = _ := by
      rw [← Algebra.discr_of_matrix_vecMul, Module.Basis.toMatrix_map_vecMul]
      exact hx
  have hn : (discr F : ℚ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hsq : P.det ^ 2 = 1 := by
    have h : (P.det : ℚ) ^ 2 = 1 :=
      mul_right_cancel₀ hn (by simpa only [one_mul] using hdet)
    exact_mod_cast h
  have hu : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨P.det, by rwa [← sq]⟩
  obtain ⟨a, ha⟩ := (Matrix.mulVec_surjective_iff_isUnit (A := P)).mpr
    ((Matrix.isUnit_iff_isUnit_det (A := P)).mpr hu) (c.repr y)
  refine ⟨a, c.repr.injective ?_⟩
  ext i
  have hi := congrFun ha i
  simpa only [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, map_sum,
    map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm] using hi.symm

private def quadraticBasisOfDiscr (h₂ : Module.finrank ℚ F = 2) (hdisc : discr F = d)
    (hneg : d < 0) (hfour : d % 4 = 1) : QuadraticBasis F d := by
  letI : Fact (¬ IsSquare (d : ℚ)) := ⟨by
    rintro ⟨q, hq⟩
    have hd : (d : ℚ) < 0 := by exact_mod_cast hneg
    rw [hq] at hd
    exact (not_lt_of_ge (mul_self_nonneg q)) hd⟩
  have hroot : ∃ r : F, r ^ 2 = (d : F) := hdisc ▸ exists_sq_eq_discr (K := F) h₂
  let r := hroot.choose
  have hr : r ^ 2 = (d : F) := hroot.choose_spec
  let f : Qsqrt d →ₐ[ℚ] F := QuadraticAlgebra.lift ⟨r, by
    simpa [← sq, Algebra.algebraMap_eq_smul_one] using hr⟩
  have hf : Function.Surjective f := by
    change Function.Surjective f.toLinearMap
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Qsqrt.finrank, h₂])).mp f.injective
  let model := AlgEquiv.ofBijective f ⟨f.injective, hf⟩
  have hm : model QuadraticAlgebra.omega = r := by
    change f QuadraticAlgebra.omega = r
    simp [f]
  let θ : F := (1 + model QuadraticAlgebra.omega) / 2
  let k : ℤ := d / 4
  have hk : d = 4 * k + 1 := by dsimp [k]; omega
  have hr' : r ^ 2 = 4 * (k : F) + 1 := by rw [hr, hk]; push_cast; ring
  have hint : IsIntegral ℤ θ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C k, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, θ, hm]
    field_simp
    linear_combination hr'
  refine ⟨model, hint, fun y => ?_⟩
  let x : Fin 2 → 𝓞 F := ![1, ⟨θ, hint⟩]
  have hx : (fun i => (x i : F)) =
      model ∘ (![1, (1 / 2 : ℚ) • (1 + QuadraticAlgebra.omega)] : Fin 2 → Qsqrt d) := by
    funext i
    fin_cases i
    · simp [x]
    · change θ = model ((1 / 2 : ℚ) • (1 + QuadraticAlgebra.omega))
      rw [Algebra.smul_def, map_mul, model.commutes, map_add, map_one, eq_ratCast]
      push_cast
      simp only [θ]
      ring
  obtain ⟨a, ha⟩ := spans_of_discr h₂ x (by
    rw [hx, ← Algebra.discr_eq_discr_of_algEquiv _ model, half_discr, hdisc]) y
  refine ⟨a 0, a 1, ?_⟩
  have h := congrArg (algebraMap (𝓞 F) F) ha
  rw [Fin.sum_univ_two, map_add, map_zsmul, map_zsmul] at h
  change (y : F) = a 0 • (1 : F) + a 1 • θ at h
  simpa [zsmul_eq_mul] using h

/-- The integral basis for the quadratic field of the odd filter.
The order generated by the half root has the field discriminant, so its index is one. -/
def quadraticBasis {D m : ℤ} (h₂ : Module.finrank ℚ F = 2) (hdisc : discr F = D * -m)
    (hneg : D * -m < 0) (hfour : (D * -m) % 4 = 1) : QuadraticBasis F (D * -m) :=
  quadraticBasisOfDiscr h₂ hdisc hneg hfour

end ZInQ.Manuscript.RC.O7Character
