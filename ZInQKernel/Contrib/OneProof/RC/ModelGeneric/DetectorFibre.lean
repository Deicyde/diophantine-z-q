import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.ShortBaseChange
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelSmooth
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The affine presentation of the detector's generic fibre -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModelTorsion
open scoped TensorProduct

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- The affine coordinate ring obtained by taking the generic fibre at a detector. -/
abbrev detectorFibreAlgebra :=
  ℚ ⊗[LocalIntegers ell] Pinned.Y0LevelAlgebra h₅ htame h₂

/-- The base change morphism from the spectrum of the detector's fraction field. -/
noncomputable def detectorRationalPoint :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (LocalIntegers ell)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))

/-- The spectrum of the tensor algebra presents the scheme-theoretic generic fibre. -/
noncomputable def detectorFibreIso :
    Over.mk (pullback.fst (detectorRationalPoint (ell := ell)) (Pinned.Y0Level h₅ htame h₂).hom) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ (detectorFibreAlgebra h₅ htame h₂)))) := by
  refine Over.isoMk (pullbackSpecIso (LocalIntegers ell) ℚ
    (Pinned.Y0LevelAlgebra h₅ htame h₂)) ?_
  exact pullbackSpecIso_hom_fst' (LocalIntegers ell) ℚ _

/-- The detector fibre's geometric points are the pinned classes of actual cyclic pairs. -/
noncomputable def detectorFibrePoints {k : Type*} [Field k] [Algebra ℚ k] [DecidableEq k]
    [IsAlgClosed k] [Algebra (LocalIntegers ell) k] [IsScalarTower (LocalIntegers ell) ℚ k] :
    (detectorFibreAlgebra h₅ htame h₂ →ₐ[ℚ] k) ≃ PairClasses k N :=
  (AlgHom.liftEquiv (LocalIntegers ell) ℚ (Pinned.Y0LevelAlgebra h₅ htame h₂) k).symm.trans
    (Pinned.Y0LevelPoints h₅ htame h₂)

/-- The source j-coordinate in the detector's generic fibre is the scalar extension of its
actual short-family invariant. -/
noncomputable def detectorFibreJ : detectorFibreAlgebra h₅ htame h₂ :=
  (1 : ℚ) ⊗ₜ[LocalIntegers ell] Pinned.Y0LevelJ h₅ htame h₂

/-- Every local ring on the scheme-theoretic generic fibre is a normal domain. -/
theorem detectorFibre_normal (q : Ideal (detectorFibreAlgebra h₅ htame h₂)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  Pinned.levelQuotient_fibre_normal h₅ htame h₂ ℚ q

#print axioms detectorFibreAlgebra
#print axioms detectorRationalPoint
#print axioms detectorFibreIso
#print axioms detectorFibrePoints
#print axioms detectorFibreJ
#print axioms detectorFibre_normal

end WeierstrassCurve.ModelLevels.ModelGeneric
