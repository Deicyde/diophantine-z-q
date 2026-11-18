import ActualFiniteQuotientV002
import ActualValuationRestrictionV002

/-!
# Closed actual finite ramification images

The finite image is the literal restriction image in the actual Galois
group. Its inherited residue characteristic comes from the original
valuation ring through the actual local scalar inclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ActualClosedFiniteImages
open ActualFiniteLevel ActualDivisionField ActualFiniteRamification ActualFiniteQuotient
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma wildImage_closed (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    IsClosed (wildImage w L : Set (L ≃ₐ[K] L)) := isClosed_discrete _

def wildClosedImage (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    ClosedSubgroup (L ≃ₐ[K] L) := ⟨wildImage w L, wildImage_closed w L⟩

lemma wildImage_isPGroup_base (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (L : FiniteGaloisIntermediateField K Ω)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] :
    IsPGroup p (wildImage w L) := by
  haveI := ActualValuationRestriction.residue_characteristic_inherited O w hw L.toIntermediateField p
  exact wildImage_isPGroup w L p

lemma wildClosedImage_isPGroup_base (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (L : FiniteGaloisIntermediateField K Ω)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] :
    IsPGroup p (wildClosedImage w L) := wildImage_isPGroup_base O w hw L p

lemma actionImage_isPGroup_base [CharZero K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (m : ℕ)
    [Finite (torsionSubgroup A Ω m)] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] :
    IsPGroup p (wildActionImage A m w) := by
  rw [wildActionImage_actual]
  exact (wildImage_isPGroup_base O w hw (finiteDivisionField A m) p).map (factoredAction A m)

end ActualClosedFiniteImages
