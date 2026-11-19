import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.PointReduction
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-! Realize good reduction on the geometric points at the chosen prime.
The discriminant condition on the integral equation can be enforced by the
finite prime exclusions in tex 8368–8369. -/

noncomputable section

open IsLocalRing WeierstrassCurve
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open ZInQ.Manuscript.RC.Stages
open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.WitnessSpec

section IntegralCurve

variable {L Γ : Type*} [Field L] [Algebra ℚ L] [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation L Γ) (C : WeierstrassCurve ℤ)

private theorem integralEquation_baseChange :
    ((C⁄ℚ)⁄L) = (C⁄L) := by
  simp only [baseChange, map_map]
  exact congrArg C.map (RingHom.ext_int _ _)

instance integralEquation_isIntegral : IsIntegral w.valuationSubring ((C⁄ℚ)⁄L) :=
  ⟨C.map (algebraMap ℤ w.valuationSubring), (integralEquation_baseChange C).trans
    (C.map_baseChange (Algebra.ofId w.valuationSubring L)).symm⟩

/-- The valuation ring model is obtained by casting the integral coefficients. -/
theorem integralEquation :
    integralModel w.valuationSubring ((C⁄ℚ)⁄L) = C.map (algebraMap ℤ w.valuationSubring) := by
  apply WeierstrassCurve.map_injective (f := algebraMap w.valuationSubring L) Subtype.val_injective
  exact (baseChange_integralModel_eq w.valuationSubring ((C⁄ℚ)⁄L)).trans
    ((C.map_baseChange (Algebra.ofId w.valuationSubring L)).trans
      (integralEquation_baseChange C).symm).symm

variable (p : ℕ)

/-- The integral equation is elliptic at every prime away from its discriminant. -/
theorem integralEquation_elliptic [hchar : CharP (ResidueField w.valuationSubring) p]
    (hg : ¬ (p : ℤ) ∣ C.Δ) :
    (integralModel w.valuationSubring ((C⁄ℚ)⁄L)).IsElliptic := by
  rw [integralEquation, isElliptic_iff, map_Δ, ← residue_ne_zero_iff_isUnit, eq_intCast, map_intCast]
  have h := @CharP.intCast_eq_zero_iff (ResidueField w.valuationSubring) _ p hchar C.Δ
  exact fun hz => hg (h.mp hz)

/-- Reduction of the integral curve uses the same prime-field curve over every
valuation residue field of characteristic p. -/
theorem integralEquation_residue [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    (integralModel w.valuationSubring ((C⁄ℚ)⁄L)).map (residue w.valuationSubring) =
      (C.map (Int.castRingHom (ZMod p))).baseChange (ResidueField w.valuationSubring) := by
  rw [integralEquation, baseChange, map_map, map_map]
  exact congrArg C.map (RingHom.ext_int _ _)


end IntegralCurve

namespace FrobeniusPlace

attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

/-- The residue equivalence in the point reduction API. -/
def valuationResidueEquiv :
    (Zbar ⧸ v.prime) ≃+* ResidueField v.valuationRing.valuation.valuationSubring :=
  v.localResidueEquiv.trans (ResidueField.mapEquiv v.localValuationEquiv)

instance valuationResidue_charP : CharP (ResidueField v.valuationRing.valuation.valuationSubring) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast v.valuationResidueEquiv, CharP.cast_eq_zero, map_zero])

instance valuationResidue_algebra :
    Algebra (ZMod p) (ResidueField v.valuationRing.valuation.valuationSubring) :=
  (ZMod.castHom (dvd_rfl : p ∣ p) (ResidueField v.valuationRing.valuation.valuationSubring)).toAlgebra

instance valuationResidue_algClosed :
    IsAlgClosed (ResidueField v.valuationRing.valuation.valuationSubring) := by
  let : IsAlgClosed (Zbar ⧸ v.prime) := v.isAlgClosed_residue
  apply IsAlgClosed.of_exists_root
  intro f hm hi
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective
    v.valuationResidueEquiv.symm.toRingHom v.valuationResidueEquiv.symm.injective f
    (by rw [Polynomial.degree_eq_natDegree hm.ne_zero]; exact_mod_cast hi.natDegree_pos.ne')
  refine ⟨v.valuationResidueEquiv x, ?_⟩
  let j := v.valuationResidueEquiv
  have h := congrArg j.toRingHom hx
  rw [map_zero, Polynomial.hom_eval₂] at h
  have hj : j.toRingHom.comp j.symm.toRingHom = RingHom.id _ := by
    ext a
    exact j.apply_symm_apply a
  rw [hj, Polynomial.eval₂_id] at h
  exact h

open scoped Classical

variable (C : WeierstrassCurve ℤ) (hg : ¬ (p : ℤ) ∣ C.Δ)

/-- Geometric reduction of E at the exact chosen prime. -/
def curveReduction :
    (((C⁄ℚ)⁄Qbar)).toAffine.Point →+
      ((C.map (Int.castRingHom (ZMod p)))⁄(ResidueField v.valuationRing.valuation.valuationSubring)).toAffine.Point := by
  letI := integralEquation_elliptic v.valuationRing.valuation C p hg
  exact reductionToModel (E := C⁄ℚ) v.valuationRing.valuation (C.map (Int.castRingHom (ZMod p)))
    (integralEquation_residue v.valuationRing.valuation C p)

/-- On all geometric curve points, the chosen global element reduces to
arithmetic Frobenius on the very same residue curve. -/
theorem curveReduction_frobenius (P : ((C⁄ℚ)⁄Qbar).toAffine.Point) :
    v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom P) =
      curveFrob (K := ResidueField v.valuationRing.valuation.valuationSubring)
        (C.map (Int.castRingHom (ZMod p))) (v.curveReduction C hg P) := by
  let := integralEquation_elliptic v.valuationRing.valuation C p hg
  exact reductionToModel_frobenius (E := C⁄ℚ) v.valuationRing.valuation (C.map (Int.castRingHom (ZMod p)))
    (integralEquation_residue v.valuationRing.valuation C p)
    g v.valuation_frob_le_one_iff v.valuation_frob_residue P


end FrobeniusPlace
end ZInQ.Manuscript.RC.WitnessSpec
