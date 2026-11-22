import ZInQKernel.Contrib.OneProof.PointedCurveFunctionField
import ZInQKernel.Contrib.OneProof.Y3P1FunctionField
import ZInQKernel.Contrib.OneProof.Y3QuotientGenusZero

/-! The rational genus-zero period quotient is the prescribed projective line. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open LeafQM.AV HDec HDec.HSyn.G0Split.FibreQM.PeriodMapH Y3RouteA

namespace Y3P1j

/-- The normalized level-three quotient and its three CM fibres follow from
the canonical level model, the period data, and CM descent. -/
theorem y3ToP1j_of_canonical_model_and_cm
    (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hL : QMTwistLattice) (hF : CMFixedHasCM) (hC : CMDescends)
    (hA : RayClassCFT.CMAnalytic) (hj : PkgI1.QMHauptmodul) :
    Y3ToP1j := by
  obtain ⟨Z, x₄, _, _, hP, hS, hInt, hg, _, _, _, hend⟩ :=
    exists_genus_zero_quotient_reducing_y3ToP1j hI hD hL hF hC hA hj
  have hSection : x₄.left ≫ Z.hom = 𝟙 _ := x₄.w.trans (by simp [fieldPt])
  obtain ⟨e⟩ := exists_ratFunc_equiv_of_arithmeticGenus_zero Z.hom x₄.left hSection hg
  apply hend
  have hdim : topologicalKrullDim Z.left = 1 :=
    ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension Z.hom 1
  let r : Z.left.functionField ≃+* RatFunc ℚ := by
    letI : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
    exact e.toRingEquiv.symm
  exact P1.nonempty_iso_PQ_of_functionField Z
    (ZInQ.Contrib.RC53Assist.S2aNumberField.smooth_curve_valuation_stalk Z.hom hdim)
    { r with commutes' := RingHom.map_rat_algebraMap r.toRingHom }

end Y3P1j

#print axioms Y3P1j.y3ToP1j_of_canonical_model_and_cm
