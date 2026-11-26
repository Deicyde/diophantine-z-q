import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.DetectorFibre
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.QuotientBaseChange

/-! # The detector-independent rational fibre as a scheme -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModelTorsion

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- The scheme-theoretic generic fibre of every admissible pinned model is
the same rational short-level quotient. -/
noncomputable def Y0RationalFibreIso :
    Over.mk (pullback.fst (detectorRationalPoint (ell := ell)) (Pinned.Y0Level h₅ htame h₂).hom) ≅
      Y0Rational h₂ := by
  let e := Y0RationalBaseChange h₅ htame h₂
  refine detectorFibreIso h₅ htame h₂ ≪≫
    Over.isoMk (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (Y0RationalAlgebra h₂))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (detectorFibreAlgebra h₅ htame h₂)))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact e.symm.commutes r

#print axioms Y0RationalFibreIso

end WeierstrassCurve.ModelLevels.ModelGeneric
