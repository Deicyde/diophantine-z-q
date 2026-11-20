import ZInQKernel.Contrib.OneProof.Y3NormalPeriodQuotient
import ZInQKernel.Contrib.OneProof.Y3QuotientCoordinate
import ZInQKernel.Contrib.OneProof.Y3CMExistence
import ZInQKernel.Contrib.OneProof.RegularSmoothPerfect

/-! The smooth rational quotient and the precise remaining projective-line
identification for the normalized level-three coordinate. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodMapH
open Y3Fix Y3RouteA

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The actual quotient is a smooth proper integral rational curve with the
printed period map and three distinct rational CM points. An algebraic
projective-line identification then supplies the original normalized
coordinate on every fine model. -/
theorem exists_smooth_period_quotient_reducing_y3ToP1j
    (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hL : QMTwistLattice) (hF : CMFixedHasCM) (hC : CMDescends)
    (hA : RayClassCFT.CMAnalytic) (hj : PkgI1.QMHauptmodul) :
    ∃ (Z : Over (Spec (CommRingCat.of ℚ))) (F : UpperHalfPlane → (fieldPt ℂ ⟶ Z))
      (x₄ x₃ x₂₄ : fieldPt ℚ ⟶ Z),
      IsProper Z.hom ∧ SmoothOfRelativeDimension 1 Z.hom ∧ IsIntegral Z.left ∧
      Function.Surjective F ∧ ShimuraSplit.IsHolFamily (fun τ => (F τ).left) ∧
      (∀ τ τ', F τ = F τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
      x₄ ≠ x₃ ∧ x₄ ≠ x₂₄ ∧ x₃ ≠ x₂₄ ∧
      (Nonempty (Z ≅ P1.PQ) → Y3ToP1j) := by
  obtain ⟨Y, Φ, Z, π, F, hΦ, hP, hInt, hNorm, hDim, _, _, hquot, hs, hhol, hOrb⟩ :=
    exists_normal_period_quotient_of_z30 hI hD hL
  have hSmooth := _root_.CurveSplit.normalCurveSmoothQ_of_regularSmooth
    ZInQ.Contrib.OneProof.RegularSmoothPerfect.regularSmoothPerfect_proof Z
    inferInstance hInt hNorm hDim
  have hE := exists_CM_objects_of_fixed_periods hΦ hD hF hC
  obtain ⟨x₄, x₃, x₂₄, h43, h424, h324, hCM⟩ :=
    exists_rational_CM_fibres_of_periods π hΦ hquot hD hL hA hj hE
  refine ⟨Z, F, x₄, x₃, x₂₄, hP, hSmooth, hInt, hs, hhol, hOrb, h43, h424, h324, ?_⟩
  rintro ⟨e⟩
  exact y3ToP1j_of_quotient_iso_and_CM_fibres π hΦ e (hquot Qbar) h43 h424 h324 hCM

end Y3P1j

#print axioms Y3P1j.exists_smooth_period_quotient_reducing_y3ToP1j
