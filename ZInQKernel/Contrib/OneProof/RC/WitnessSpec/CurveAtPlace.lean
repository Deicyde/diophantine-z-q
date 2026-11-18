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

local notation "R" => (Valuation.valuationSubring w)
local notation "k" => (ResidueField R)

private theorem integralEquation_baseChange :
    ((C⁄ℚ)⁄L) = (C⁄L) := by
  simp only [baseChange, map_map]
  exact congrArg C.map (RingHom.ext_int _ _)

instance integralEquation_isIntegral : IsIntegral R ((C⁄ℚ)⁄L) :=
  ⟨C.map (algebraMap ℤ R), (integralEquation_baseChange C).trans
    (C.map_baseChange (Algebra.ofId R L)).symm⟩

/-- The valuation ring model is obtained by casting the integral coefficients. -/
theorem integralEquation :
    integralModel R ((C⁄ℚ)⁄L) = C.map (algebraMap ℤ R) := by
  apply WeierstrassCurve.map_injective (f := algebraMap R L) Subtype.val_injective
  exact (baseChange_integralModel_eq R ((C⁄ℚ)⁄L)).trans
    ((C.map_baseChange (Algebra.ofId R L)).trans (integralEquation_baseChange C).symm).symm

variable (p : ℕ)

/-- The integral equation is elliptic at every prime away from its discriminant. -/
theorem integralEquation_elliptic [hchar : CharP (ResidueField w.valuationSubring) p]
    (hg : ¬ (p : ℤ) ∣ C.Δ) :
    (integralModel R ((C⁄ℚ)⁄L)).IsElliptic := by
  rw [integralEquation, isElliptic_iff, map_Δ, ← residue_ne_zero_iff_isUnit, eq_intCast, map_intCast]
  have h := @CharP.intCast_eq_zero_iff (ResidueField w.valuationSubring) _ p hchar C.Δ
  exact fun hz => hg (h.mp hz)

/-- Reduction of the integral curve uses the same prime-field curve over every
valuation residue field of characteristic p. -/
theorem integralEquation_residue [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    (integralModel R ((C⁄ℚ)⁄L)).map (residue R) =
      (C.map (Int.castRingHom (ZMod p))).baseChange (ResidueField w.valuationSubring) := by
  rw [integralEquation, baseChange, map_map, map_map]
  exact congrArg C.map (RingHom.ext_int _ _)

#print axioms integralEquation_baseChange
#print axioms integralEquation_isIntegral
#print axioms integralEquation
#print axioms integralEquation_elliptic
#print axioms integralEquation_residue

end IntegralCurve

namespace FrobeniusPlace

attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

local notation "wₚ" => (ValuationSubring.valuation (valuationRing v))
local notation "Rₚ" => (Valuation.valuationSubring wₚ)
local notation "kₚ" => (ResidueField Rₚ)

/-- The residue equivalence in the point reduction API. -/
def valuationResidueEquiv : (Zbar ⧸ v.prime) ≃+* kₚ :=
  v.localResidueEquiv.trans (ResidueField.mapEquiv v.localValuationEquiv)

instance valuationResidue_charP : CharP kₚ p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast v.valuationResidueEquiv, CharP.cast_eq_zero, map_zero])

instance valuationResidue_algebra : Algebra (ZMod p) kₚ :=
  (ZMod.castHom (dvd_rfl : p ∣ p) kₚ).toAlgebra

instance valuationResidue_algClosed : IsAlgClosed kₚ := by
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

local notation "B" => (WeierstrassCurve.map C (Int.castRingHom (ZMod p)))

/-- Geometric reduction of E at the exact chosen prime. -/
def curveReduction :
    (((C⁄ℚ)⁄Qbar)).toAffine.Point →+ (B⁄kₚ).toAffine.Point := by
  letI := integralEquation_elliptic wₚ C p hg
  exact reductionToModel (E := C⁄ℚ) wₚ B (integralEquation_residue wₚ C p)

/-- On all geometric curve points, the chosen global element reduces to
arithmetic Frobenius on the very same residue curve. -/
theorem curveReduction_frobenius (P : ((C⁄ℚ)⁄Qbar).toAffine.Point) :
    v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom P) =
      curveFrob (K := kₚ) B (v.curveReduction C hg P) := by
  let := integralEquation_elliptic wₚ C p hg
  exact reductionToModel_frobenius (E := C⁄ℚ) wₚ B (integralEquation_residue wₚ C p)
    g v.valuation_frob_le_one_iff v.valuation_frob_residue P

#print axioms valuationResidueEquiv
#print axioms valuationResidue_charP
#print axioms valuationResidue_algebra
#print axioms valuationResidue_algClosed
#print axioms curveReduction
#print axioms curveReduction_frobenius

end FrobeniusPlace
end ZInQ.Manuscript.RC.WitnessSpec
