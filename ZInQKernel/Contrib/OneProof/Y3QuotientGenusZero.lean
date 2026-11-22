import ZInQKernel.Contrib.OneProof.AlgebraicHolomorphicCovector
import ZInQKernel.Contrib.OneProof.CurvePositiveGenusDifferential
import ZInQKernel.Contrib.OneProof.PointedRationalCurve
import ZInQKernel.Contrib.OneProof.Y3ComplexBaseChangeTopology
import ZInQKernel.Contrib.OneProof.Y3SmoothPeriodQuotient
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FieldExtension

/-! The actual smooth period quotient has arithmetic genus zero. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules
open LeafQM.AV HDec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

namespace AlgebraicGeometry.Curve

/-- A smooth proper complex curve whose complex points form a sphere has
arithmetic genus zero. -/
theorem arithmeticGenus_eq_zero_of_complex_sphere (C : Curve ℂ)
    (e : ComplexPoint C.carrier ≃ₜ OnePoint ℂ) :
    letI : C.carrier.left.Over (Spec (.of ℂ)) := ⟨C.carrier.hom⟩
    C.carrier.left.arithmeticGenus ℂ = 0 := by
  let _ : C.carrier.left.Over (Spec (.of ℂ)) := ⟨C.carrier.hom⟩
  apply Nat.eq_zero_of_not_pos
  intro h
  obtain ⟨w, hw⟩ := C.exists_nonzero_global_differential_of_pos_genus h
  let j := H.zeroLinearEquiv C.carrier.hom.relativeDifferentials
  exact hw (j.injective ((ComplexPoint.relativeDifferentialSection_eq_zero_of_complex_sphere
    e (j w)).trans j.map_zero.symm))

end AlgebraicGeometry.Curve

namespace Y3P1j

/-- A pointed proper smooth integral rational curve with spherical native
complex points has arithmetic genus zero over the rational field. -/
theorem arithmeticGenus_eq_zero_of_complex_baseChange_sphere
    (X : Over (Spec (CommRingCat.of ℚ))) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsIntegral X.left]
    (p : fieldPt ℚ ⟶ X) (e : ComplexPoint (complexBaseChange X) ≃ₜ OnePoint ℂ) :
    letI : X.left.Over (Spec (.of ℚ)) := ⟨X.hom⟩
    X.left.arithmeticGenus ℚ = 0 := by
  let _ : X.left.Over (Spec (.of ℚ)) := ⟨X.hom⟩
  have hp : p.left ≫ X.hom = 𝟙 _ := p.w.trans (by simp [fieldPt])
  have : IsProper (X.left ↘ Spec (.of ℚ)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIrreducible X.hom :=
    geometricallyIrreducible_of_proper_smooth_integral_section X.hom p.left hp
  let f := pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))
  have : IsProper (complexBaseChange X).hom := inferInstanceAs (IsProper f)
  have : SmoothOfRelativeDimension 1 (complexBaseChange X).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 f)
  have : GeometricallyIrreducible (complexBaseChange X).hom :=
    inferInstanceAs (GeometricallyIrreducible f)
  let C : Curve ℂ := ⟨complexBaseChange X⟩
  have h := C.arithmeticGenus_eq_zero_of_complex_sphere e
  exact (Scheme.arithmeticGenus_pullback ℂ).symm.trans h

open HDec.HSyn.G0Split.FibreQM.PeriodMapH Y3RouteA in
/-- The actual quotient that reduces the normalized level-three theorem
has arithmetic genus zero and three distinct rational CM points. -/
theorem exists_genus_zero_quotient_reducing_y3ToP1j
    (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hL : QMTwistLattice) (hF : CMFixedHasCM) (hC : CMDescends)
    (hA : RayClassCFT.CMAnalytic) (hj : PkgI1.QMHauptmodul) :
    ∃ (Z : Over (Spec (CommRingCat.of ℚ))) (x₄ x₃ x₂₄ : fieldPt ℚ ⟶ Z),
      IsProper Z.hom ∧ SmoothOfRelativeDimension 1 Z.hom ∧ IsIntegral Z.left ∧
      (letI : Z.left.Over (Spec (.of ℚ)) := ⟨Z.hom⟩; Z.left.arithmeticGenus ℚ = 0) ∧
      x₄ ≠ x₃ ∧ x₄ ≠ x₂₄ ∧ x₃ ≠ x₂₄ ∧
      (Nonempty (Z ≅ P1.PQ) → Y3ToP1j) := by
  obtain ⟨Z, F, x₄, x₃, x₂₄, hP, hS, hInt, hs, hhol, horb, h43, h424, h324, Hend⟩ :=
    exists_smooth_period_quotient_reducing_y3ToP1j hI hD hL hF hC hA hj
  let _ : TopologicalSpace (fieldPt ℂ ⟶ Z) := complexPointTopology Z
  obtain ⟨e⟩ := complexPoints_homeomorphic_sphere Z hs hhol horb hj
  have hg := arithmeticGenus_eq_zero_of_complex_baseChange_sphere Z x₄
    ((complexPointBaseChangeHomeomorph Z).trans e)
  exact ⟨Z, x₄, x₃, x₂₄, hP, hS, hInt, hg, h43, h424, h324, Hend⟩

end Y3P1j

#print axioms Y3P1j.exists_genus_zero_quotient_reducing_y3ToP1j
