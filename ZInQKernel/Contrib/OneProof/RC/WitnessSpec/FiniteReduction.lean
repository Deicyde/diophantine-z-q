import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.CurveAtPlace
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.RingClassPlace

/-! Use the same residue curve for the absolute place and its restrictions. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (Qbar GQ)
open ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory WeierstrassCurve
open scoped NumberField WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
variable {L : Type*} [Field L] [NumberField L] (e : L →ₐ[ℚ] Qbar)

instance finiteResidue_charP :
    CharP (ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring) p := by
  let : CharP (ResidueField v.valuationRing.valuation.valuationSubring) p := v.valuationResidue_charP
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  apply (v.valuationResidueMap e).injective
  rw [map_natCast, map_zero, CharP.cast_eq_zero]

instance finiteResidue_algebra :
    Algebra (ZMod p) (ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring) :=
  (ZMod.castHom (dvd_rfl : p ∣ p)
    (ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring)).toAlgebra

/-- The finite residue embedding as a map over the common prime field. -/
def residueEmbedding :
    (ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring) →ₐ[ZMod p]
      ResidueField v.valuationRing.valuation.valuationSubring :=
  ⟨v.valuationResidueMap e, fun a => by
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
    let kL := ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring
    change v.valuationResidueMap e (algebraMap (ZMod p) kL (i : ZMod p)) =
      algebraMap (ZMod p) (ResidueField v.valuationRing.valuation.valuationSubring) (i : ZMod p)
    simp only [map_intCast]⟩

variable (C : WeierstrassCurve ℤ) (hg : ¬ (p : ℤ) ∣ C.Δ)

/-- Reduction at the contracted place on the finite field. -/
def finiteReduction :
    ((C⁄ℚ)⁄L).toAffine.Point →+
      ((C.map (Int.castRingHom (ZMod p)))⁄
        (ResidueField ((v.restrictHeightOne e).valuation L).valuationSubring)).toAffine.Point := by
  letI := integralEquation_elliptic ((v.restrictHeightOne e).valuation L) C p hg
  exact reductionToModel (E := C⁄ℚ) ((v.restrictHeightOne e).valuation L)
    (C.map (Int.castRingHom (ZMod p)))
    (integralEquation_residue ((v.restrictHeightOne e).valuation L) C p)

/-- Reduction and passage to the algebraic closure commute on all points. -/
theorem finiteReduction_agrees (P : ((C⁄ℚ)⁄L).toAffine.Point) :
    v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) e P) =
      Affine.Point.map (W' := C.map (Int.castRingHom (ZMod p)))
        (v.residueEmbedding e) (v.finiteReduction e C hg P) := by
  let := integralEquation_elliptic ((v.restrictHeightOne e).valuation L) C p hg
  let := integralEquation_elliptic v.valuationRing.valuation C p hg
  exact reductionToModel_natural (E := C⁄ℚ) ((v.restrictHeightOne e).valuation L)
    (C.map (Int.castRingHom (ZMod p)))
    v.valuationRing.valuation (integralEquation_residue ((v.restrictHeightOne e).valuation L) C p)
    (integralEquation_residue v.valuationRing.valuation C p)
    e (v.residueEmbedding e) (v.valuation_le_one_restrict e)
    (v.valuationResidueMap_residue e) P

variable {K : Type} [Field K] [NumberField K]
  (er : ringClassField (conductorOrder K 1) →ₐ[ℚ] Qbar)
  (hK : Module.finrank ℚ K = 2) (hD : ¬ (p : ℤ) ∣ discr K)
  (hsign : legendreSym p (discr K) = -1)

/-- Reduction of the ring class point into the square-fixed group used by κ. -/
def ringClassReduction (hg : ¬ (p : ℤ) ∣ C.Δ) :
    letI := Classical.decEq (ringClassField (conductorOrder K 1))
    ((C⁄ℚ)⁄(ringClassField (conductorOrder K 1))).toAffine.Point →+
      Stages.FixedSq (Stages.curveFrob (K := ResidueField v.valuationRing.valuation.valuationSubring)
        (C.map (Int.castRingHom (ZMod p)))) := by
  letI := Classical.decEq (ringClassField (conductorOrder K 1))
  let kH := ResidueField
    ((v.restrictHeightOne er).valuation (ringClassField (conductorOrder K 1))).valuationSubring
  have hcard : Nat.card kH = p ^ 2 :=
    (Nat.card_congr (v.finiteValuationResidueEquiv er).toEquiv).symm.trans
      (v.ringClassResidue_card er hK hD hsign)
  letI : Finite kH :=
    Nat.finite_of_card_ne_zero (hcard.symm ▸ pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  exact (quadraticResiduePoints hcard (C.map (Int.castRingHom (ZMod p))) (v.residueEmbedding er)).comp
    (v.finiteReduction er C hg)

/-- The descended ring class reduction is the reduction at the exact same absolute place. -/
theorem ringClassReduction_agrees (P : ((C⁄ℚ)⁄(ringClassField (conductorOrder K 1))).toAffine.Point) :
    letI := Classical.decEq (ringClassField (conductorOrder K 1))
    (v.ringClassReduction C er hK hD hsign hg P).val =
      v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) er P) :=
  (v.finiteReduction_agrees er C hg P).symm


end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
