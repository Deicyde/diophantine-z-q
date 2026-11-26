import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.FieldComparison
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Geometric integrality of the pinned rational open -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open ModelGeneric ModularCurve
open ZInQ.Manuscript.RC
open scoped TensorProduct

attribute [local instance] X0Model.jAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 70000

private noncomputable def extendLaurentCoefficients (k : Type*) [Field k] [Algebra ℚ k] :
    LaurentSeries ℚ →ₐ[ℚ] LaurentSeries k :=
  ⟨coeffEmb k, fun q => DFunLike.congr_fun
    (Subsingleton.elim ((coeffEmb k).comp (algebraMap ℚ (LaurentSeries ℚ)))
      (algebraMap ℚ (LaurentSeries k))) q⟩

private theorem tensor_isDomain_of_laurentEmbedding
    {B k : Type*} [CommRing B] [Algebra ℚ B] [Field k] [Algebra ℚ k]
    (φ : B →ₐ[ℚ] LaurentSeries ℚ) (hφ : Function.Injective φ) :
    IsDomain (B ⊗[ℚ] k) := by
  classical
  let f : B →ₐ[ℚ] LaurentSeries k := (extendLaurentCoefficients k).comp φ
  let g : k →ₐ[ℚ] LaurentSeries k := ⟨algebraMap k (LaurentSeries k), fun q =>
    DFunLike.congr_fun (Subsingleton.elim
      ((algebraMap k (LaurentSeries k)).comp (algebraMap ℚ k)) (algebraMap ℚ (LaurentSeries k))) q⟩
  let h : B ⊗[ℚ] k →ₐ[ℚ] LaurentSeries k := Algebra.TensorProduct.productMap f g
  apply Function.Injective.isDomain h
  apply (injective_iff_map_eq_zero h).mpr
  intro x hx
  let b := Module.Free.chooseBasis ℚ k
  let w := TensorProduct.equivFinsuppOfBasisRight (M := B) b x
  have hsum : w.sum (fun i u => u ⊗ₜ[ℚ] b i) = x := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    exact (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply x
  have hcoeff (n : ℤ) : ∑ i ∈ w.support, (φ (w i)).coeff n • b i = 0 := by
    have eq : (h (w.sum (fun i u => u ⊗ₜ[ℚ] b i))).coeff n = 0 := by
      rw [hsum, hx, HahnSeries.coeff_zero]
    unfold Finsupp.sum at eq
    rw [map_sum, HahnSeries.coeff_sum] at eq
    refine (Finset.sum_congr rfl fun i _ => ?_).trans eq
    change (φ (w i)).coeff n • b i = (Algebra.TensorProduct.productMap f g
      (w i ⊗ₜ[ℚ] b i)).coeff n
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change (φ (w i)).coeff n • b i = (f (w i) * algebraMap k (LaurentSeries k) (b i)).coeff n
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_mul_single_zero]
    exact Algebra.smul_def _ _
  have hw : w = 0 := by
    ext i
    by_contra hi
    have hm : i ∈ w.support := Finsupp.mem_support_iff.mpr hi
    have hzero : φ (w i) = φ 0 := by
      rw [map_zero]
      ext n
      rw [HahnSeries.coeff_zero]
      exact (linearIndependent_iff'.mp b.linearIndependent) w.support
        (fun t => (φ (w t)).coeff n) (hcoeff n) i hm
    exact hi (hφ hzero)
  exact (TensorProduct.equivFinsuppOfBasisRight b).injective (hw.trans (map_zero _).symm)

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The pinned rational coordinate algebra remains a domain after extending
the ground field. A rational Laurent-series embedding gives an embedding
after any scalar extension, by reading coefficients in a ground-field basis. -/
theorem rationalAlgebra_baseChange_isDomain {k : Type*} [Field k] [Algebra ℚ k] :
    IsDomain (k ⊗[ℚ] Y0RationalAlgebra h₂) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  let e := genericModularFieldEquiv h₂ data
  let f := (modularFunctionField N).toSubfield.subtype.comp
    (e.toRingHom.comp (Y0RationalGenericJInclusion h₂))
  let φ : Y0RationalAlgebra h₂ →ₐ[ℚ] LaurentSeries ℚ :=
    ⟨f, fun q => DFunLike.congr_fun (Subsingleton.elim
      (f.comp (algebraMap ℚ (Y0RationalAlgebra h₂))) (algebraMap ℚ (LaurentSeries ℚ))) q⟩
  have hi : Function.Injective φ :=
    Subtype.val_injective.comp (e.injective.comp (Y0RationalGenericJInclusion_injective h₂))
  letI := tensor_isDomain_of_laurentEmbedding (k := k) φ hi
  exact Function.Injective.isDomain (Algebra.TensorProduct.comm ℚ k (Y0RationalAlgebra h₂)).toAlgHom
    (Algebra.TensorProduct.comm ℚ k (Y0RationalAlgebra h₂)).injective

#print axioms extendLaurentCoefficients
#print axioms tensor_isDomain_of_laurentEmbedding
#print axioms rationalAlgebra_baseChange_isDomain

end WeierstrassCurve.ModelLevels.ModelGeneric2
