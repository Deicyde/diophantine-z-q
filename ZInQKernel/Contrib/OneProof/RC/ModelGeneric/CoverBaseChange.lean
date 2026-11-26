import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.ShortBaseChange
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.BaseChange

/-! # Base change of the exact-order cover on the universal short locus -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion Algebra
open scoped TensorProduct

section Exact

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (W : WeierstrassCurve A) [W.IsElliptic] (hn : IsUnit ((n + 2 : ℕ) : A))

private noncomputable def exactOrderCurveCongr {V V' : WeierstrassCurve B}
    [V.IsElliptic] [V'.IsElliptic] (h : V = V') (hN : IsUnit ((n + 2 : ℕ) : B)) :
    ExactOrderAlgebra V hN ≃ₐ[B] ExactOrderAlgebra V' hN := by
  cases h
  exact AlgEquiv.refl

end Exact

section Short

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  (hB : IsUnit ((n + 2 : ℕ) : ShortBase B))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]
  [Algebra B (ExactOrderAlgebra (shortFamily B) hB)]
  [IsScalarTower B (ShortBase B) (ExactOrderAlgebra (shortFamily B) hB)]

/-- Coefficient base change for the short cover, before canceling the short coefficient ring. -/
noncomputable def shortCoverCoefficientBaseChange :
    ShortBase B ⊗[ShortBase R] ExactOrderAlgebra (shortFamily R) hn ≃ₐ[ShortBase B]
      ExactOrderAlgebra (shortFamily B) hB :=
  (exactOrderBaseChange (B := ShortBase B) (shortFamily R) hn).trans
    (exactOrderCurveCongr shortFamily_map_shortBaseMap hB)

/-- Scalar extension of the whole marked cover. -/
noncomputable def shortCoverBaseChange :
    B ⊗[R] ExactOrderAlgebra (shortFamily R) hn ≃ₐ[B]
      ExactOrderAlgebra (shortFamily B) hB := by
  letI := shortBase_isPushout (R := R) (B := B)
  exact (IsPushout.cancelBaseChangeAlg R B (ShortBase R) (ShortBase B) _).symm.trans
    ((shortCoverCoefficientBaseChange hn hB).restrictScalars B)

private theorem shortCoverBaseChange_tmul_one
    (x : ExactOrderAlgebra (shortFamily R) hn) :
    shortCoverBaseChange hn hB ((1 : B) ⊗ₜ[R] x) =
      shortCoverCoefficientBaseChange hn hB ((1 : ShortBase B) ⊗ₜ[ShortBase R] x) := by
  haveI := shortBase_isPushout (R := R) (B := B)
  simp only [shortCoverBaseChange, AlgEquiv.trans_apply, IsPushout.cancelBaseChangeAlg_symm_tmul,
    map_one, AlgEquiv.restrictScalars_apply]

private theorem shortCoverCoefficientBaseChange_algebraMap (a : ShortBase R) :
    shortCoverCoefficientBaseChange hn hB
        ((1 : ShortBase B) ⊗ₜ[ShortBase R] algebraMap (ShortBase R) _ a) =
      algebraMap (ShortBase B) _ (algebraMap (ShortBase R) (ShortBase B) a) := by
  rw [← Algebra.TensorProduct.algebraMap_apply']
  exact (shortCoverCoefficientBaseChange hn hB).commutes (algebraMap (ShortBase R) (ShortBase B) a)

end Short

#print axioms exactOrderCurveCongr
#print axioms shortCoverCoefficientBaseChange
#print axioms shortCoverBaseChange
#print axioms shortCoverBaseChange_tmul_one
#print axioms shortCoverCoefficientBaseChange_algebraMap

end WeierstrassCurve.ModelLevels.ModelGeneric
