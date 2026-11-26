import ZInQKernel.Contrib.OneProof.NeronExtAb
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.ShortBaseChange

/-! The target of the detector parametrization, tex 8476–8479.
The detector localization is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve WeierstrassCurve.ModelTorsion
  WeierstrassCurve.ModelLevels.ModelGeneric

namespace ZInQ.Manuscript.RC.ModelNeron

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (ell : ℕ) [Fact ell.Prime]

private theorem integerPrimeIdeal_ne_bot : integerPrimeIdeal ell ≠ ⊥ := by
  simp [integerPrimeIdeal, (Fact.out : ell.Prime).ne_zero]

/-- The mapping property for a smooth proper group model at the detector. -/
theorem goodModel_neron (E : Over (Spec (.of (LocalIntegers ell))))
    [GrpObj E] [Smooth E.hom] [IsProper E.hom] :
    CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E := by
  letI := rational_isFractionRing ell
  letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (integerPrimeIdeal_ne_bot ell) (LocalIntegers ell)
  exact NeronExt.isNeronModelOver_of_grpObj (LocalIntegers ell) ℚ E

/-- An integral equation whose discriminant is prime to the detector has unit
discriminant after localization. -/
theorem isElliptic_at_detector (C : WeierstrassCurve ℤ) (hΔ : ¬ (ell : ℤ) ∣ C.Δ) :
    (C.map (algebraMap ℤ (LocalIntegers ell))).IsElliptic := by
  constructor
  rw [WeierstrassCurve.map_Δ]
  exact IsLocalization.map_units (LocalIntegers ell)
    (⟨C.Δ, by simpa [integerPrimeIdeal, Ideal.mem_span_singleton] using hΔ⟩ :
      (integerPrimeIdeal ell).primeCompl)

/-- The detector's actual projective Weierstrass cubic, with its structure map. -/
def weierstrassModel (W : WeierstrassCurve (LocalIntegers ell)) :
    Over (Spec (.of (LocalIntegers ell))) :=
  Over.mk (Proj.toSpecZero W.toProjective.grading ≫
    Spec.map W.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom)

/-- The projective cubic is proper over the detector ring. -/
theorem weierstrassModel_proper (W : WeierstrassCurve (LocalIntegers ell)) :
    IsProper (weierstrassModel ell W).hom := by
  change IsProper (Proj.toSpecZero W.toProjective.grading ≫
    Spec.map W.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom)
  infer_instance

/-- On the good cubic the smooth structure and scheme group law suffice for the
Néron mapping property. -/
theorem weierstrassModel_neron (W : WeierstrassCurve (LocalIntegers ell))
    [GrpObj (weierstrassModel ell W)] [Smooth (weierstrassModel ell W).hom] :
    CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ (weierstrassModel ell W) := by
  letI := weierstrassModel_proper ell W
  exact goodModel_neron ell (weierstrassModel ell W)

#print axioms integerPrimeIdeal_ne_bot
#print axioms goodModel_neron
#print axioms isElliptic_at_detector
#print axioms weierstrassModel
#print axioms weierstrassModel_proper
#print axioms weierstrassModel_neron

end ZInQ.Manuscript.RC.ModelNeron
