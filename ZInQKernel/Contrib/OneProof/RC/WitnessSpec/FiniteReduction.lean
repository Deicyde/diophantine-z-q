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

local notation "wₚ" => (ValuationSubring.valuation (valuationRing v))
local notation "kₚ" => (ResidueField (Valuation.valuationSubring wₚ))
local notation "wL" => (IsDedekindDomain.HeightOneSpectrum.valuation L (restrictHeightOne v e))
local notation "kL" => (ResidueField (Valuation.valuationSubring wL))

instance finiteResidue_charP : CharP kL p := by
  let : CharP kₚ p := v.valuationResidue_charP
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  apply (v.valuationResidueMap e).injective
  rw [map_natCast, map_zero, CharP.cast_eq_zero]

instance finiteResidue_algebra : Algebra (ZMod p) kL :=
  (ZMod.castHom (dvd_rfl : p ∣ p) kL).toAlgebra

/-- The finite residue embedding as a map over the common prime field. -/
def residueEmbedding : kL →ₐ[ZMod p] kₚ :=
  ⟨v.valuationResidueMap e, fun a => by
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
    change v.valuationResidueMap e (algebraMap (ZMod p) kL (i : ZMod p)) =
      algebraMap (ZMod p) kₚ (i : ZMod p)
    simp only [map_intCast]⟩

variable (C : WeierstrassCurve ℤ) (hg : ¬ (p : ℤ) ∣ C.Δ)

local notation "B" => (WeierstrassCurve.map C (Int.castRingHom (ZMod p)))

/-- Reduction at the contracted place on the finite field. -/
def finiteReduction : ((C⁄ℚ)⁄L).toAffine.Point →+ (B⁄kL).toAffine.Point := by
  letI := integralEquation_elliptic wL C p hg
  exact reductionToModel (E := C⁄ℚ) wL B (integralEquation_residue wL C p)

/-- Reduction and passage to the algebraic closure commute on all points. -/
theorem finiteReduction_agrees (P : ((C⁄ℚ)⁄L).toAffine.Point) :
    v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) e P) =
      Affine.Point.map (W' := B) (v.residueEmbedding e) (v.finiteReduction e C hg P) := by
  let := integralEquation_elliptic wL C p hg
  let := integralEquation_elliptic wₚ C p hg
  exact reductionToModel_natural (E := C⁄ℚ) wL B wₚ
    (integralEquation_residue wL C p) (integralEquation_residue wₚ C p)
    e (v.residueEmbedding e) (v.valuation_le_one_restrict e)
    (v.valuationResidueMap_residue e) P

variable {K : Type} [Field K] [NumberField K]
  (er : ringClassField (conductorOrder K 1) →ₐ[ℚ] Qbar)
  (hK : Module.finrank ℚ K = 2) (hD : ¬ (p : ℤ) ∣ discr K)
  (hsign : legendreSym p (discr K) = -1)

local notation "H" => (ringClassField (conductorOrder K 1))
local notation "kH" => (ResidueField (Valuation.valuationSubring
  (IsDedekindDomain.HeightOneSpectrum.valuation H (restrictHeightOne v er))))

/-- Reduction of the ring class point into the square-fixed group used by κ. -/
def ringClassReduction (hg : ¬ (p : ℤ) ∣ C.Δ) :
    letI := Classical.decEq H
    ((C⁄ℚ)⁄H).toAffine.Point →+
      Stages.FixedSq (Stages.curveFrob (K := kₚ) B) := by
  letI := Classical.decEq H
  have hcard : Nat.card kH = p ^ 2 :=
    (Nat.card_congr (v.finiteValuationResidueEquiv er).toEquiv).symm.trans
      (v.ringClassResidue_card er hK hD hsign)
  letI : Finite kH := Nat.finite_of_card_ne_zero
    (hcard.symm ▸ pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  exact (quadraticResiduePoints hcard B (v.residueEmbedding er)).comp (v.finiteReduction er C hg)

/-- The descended ring class reduction is the reduction at the exact same absolute place. -/
theorem ringClassReduction_agrees (P : ((C⁄ℚ)⁄H).toAffine.Point) :
    letI := Classical.decEq H
    (v.ringClassReduction C er hK hD hsign hg P).val =
      v.curveReduction C hg (Affine.Point.map (W' := C⁄ℚ) er P) :=
  (v.finiteReduction_agrees er C hg P).symm

#print axioms finiteResidue_charP
#print axioms finiteResidue_algebra
#print axioms residueEmbedding
#print axioms finiteReduction
#print axioms finiteReduction_agrees
#print axioms ringClassReduction
#print axioms ringClassReduction_agrees

end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
