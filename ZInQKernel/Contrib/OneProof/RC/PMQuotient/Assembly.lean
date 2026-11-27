import ZInQKernel.Contrib.OneProof.RC.PMQuotient.CM
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Cusps
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Assembly

/-! The (O.7) family of the total selector (tex 9101–9113, 9283–9291):
glue (c) to the existing constructor at the pinned newform signs. -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 2600
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMQuotient

open PreparedParam O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose
  SelectorTotal AtkinPin PicardFibers Eichler Adelic ThetaJoin

attribute [local irreducible] StageKummer.datumOnModel ringClassArtinEquiv GoodRow.specialFibre

variable {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) {L : ℕ}
  (s : StageKummer.Setup (genusInstance a) L)
  [NeZero (CST.newformLevel (Ecurve ℓ))] (F : ConsumerNewform (genusInstance a))
  [NeZero (StageKummer.level ℓ)] [((EcurveZ ℓ)⁄ℚ).IsElliptic]

variable (π : (X0Model3.model (StageKummer.level ℓ)).X ⟶ Proj ((EcurveZ ℓ)⁄ℚ).toProjective.grading)
  (hQ : π ≫ projectiveOverQ ((EcurveZ ℓ)⁄ℚ) = (X0Model3.model (StageKummer.level ℓ)).overQ)
  (han : ∀ τ : UpperHalfPlane, projectiveValue
    (((X0Model3.model (StageKummer.level ℓ)).complexPoint τ).comp π hQ).val =
      phiAn ((EcurveZ ℓ)⁄ℚ) (StageKummer.formOnModel (f := a.f) (EcurveZ_baseChange ℓ)) a.Lat a.κ τ)

variable {R : ℕ → Type} [∀ i, CommRing (R i)] [∀ i, Algebra (R i) ℚ]
  {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p)
  (hm : (m : ℤ) = -(withParamIndices a).hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (O : ∀ i, PMAdelic.OperatorComparison (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i) (J i))
  (G : ∀ i, GoodRow (R i) (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p)
    (X i) (fixedMap (C := EcurveZ ℓ) π hQ))
  (relations : ∀ i, (G i).Relations ap F.signs)
  (cusps : ∀ i, (G i).CuspInput L)

/-- All special fibres in the staged family use the same fixed rational
parametrization and its Néron extension at their respective places. -/
abbrev signedFamily (i : ℕ) := (G i).specialFibre (relations i)

/-- Forget the pinned signs to supply the existing PM interface. -/
abbrev fibreFamily (i : ℕ) := (signedFamily a s F π hQ G relations i).toSpecialFibre

include cusps in
/-- The translation is killed in exactly the geometry used by the actual family. -/
theorem hCuspAt (i : ℕ) (j : Fin (StageKummer.level ℓ).primeFactors.card) :
    L • (PMAdelic.geometry (J i) (O i) (fibreFamily a s F π hQ G relations i)).cusp (levelPrime _ j).val = 0 :=
  (G i).hCusp (cusps i) (relations i) (J i) (O i) _ (levelPrime _ j).prop (levelPrime_exp hN j)

section Reference

variable (i : ℕ) (D : ℤ) (hD : (withParamIndices a).admissible i D)

/-- The only selected-row inputs left after replacing `hπ` by the
integral diagram. The conductor-one CM orbit assertion remains separate. -/
structure Reference where
  /-- The selected field inside the quaternion algebra at this stage. -/
  embedding :
    let t := StageKummer.chosenDatum (I := genusInstance a) (D := (D.toNat : ℤ))
      (selectedDatum a s i D hD).val
    letI := t.field
    letI := t.nf
    t.K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ))
  /-- The orientation of the reference reduction. -/
  ref : Orientations (StageKummer.level ℓ).primeFactors.card
  /-- The actual coarse CM reductions (before reading the parametrization). -/
  r : let t := (selectedDatum a s i D hD).val
    let A := admissibleNatAt s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i D hD
    (supportAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) (fibreFamily a s F π hQ G relations i) A t).classGroup →
      (X i).Point
  /-- Geometric conductor-one reduction compared with the reference orbit. -/
  hCM : let t := (selectedDatum a s i D hD).val
    let S := fibreFamily a s F π hQ G relations i
    let A := admissibleNatAt s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i D hD
    ∀ c, r c = ((J i).idealClasses (Visibility.ThetaStage.zc
      (orbitsAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) S A t embedding
        (chartAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) S A t embedding)
        (realizationsAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) S A t embedding)).param (ref, c))).val
  /-- Comparison with the actual geometric source and elliptic lifts. -/
  diagram : let t := (selectedDatum a s i D hD).val
    let S := fibreFamily a s F π hQ G relations i
    let A := admissibleNatAt s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i D hD
    CMDiagram (C := EcurveZ ℓ) (StageKummer.chosenDatum (I := genusInstance a) (D := (D.toNat : ℤ)) t)
      (StageKummer.place s i)
      (StageKummer.chosenDatumPlace s i t
        (show stageTest s.q i (D.toNat : ℤ) from A.detecting))
      (StageKummer.goodAt s i) π hQ (G i) r
      (artinLabelAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) S A t)

include han in
/-- The exact `O7Residual.At` pointwise premise, for the actual selector,
Artin label and `StageKummer.reduceDatum`. -/
theorem hpiAt (P : Reference a s F π hQ hN hcop H hm J O G relations i D hD) :
    let t := (selectedDatum a s i D hD).val
    let S := fibreFamily a s F π hQ G relations i
    let A := admissibleNatAt s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i D hD
    ∀ c, (PMAdelic.geometricInput (J i) (O i) S).specialize (P.r c) =
      StageKummer.reduceDatum s i t (show stageTest s.q i (D.toNat : ℤ) from A.detecting)
        (conjugate (StageKummer.chosenDatum (I := genusInstance a) (D := (D.toNat : ℤ)) t)
          (artinLabelAt s i hN (hcop i) (H i) F.signs hm (J i) (O i) S A t c)) :=
  hpi_of_cmDiagram (C := EcurveZ ℓ) _ _ _ _ π hQ (G i) P.r _ (relations i) (J i) (O i) han P.diagram

/-- Fill the selector's point input using the proved specialization square. -/
def referenceComparisons (P : Reference a s F π hQ hN hcop H hm J O G relations i D hD) :
    PointComparisons s i hN (hcop i) (H i) F.signs hm (J i) (O i) (fibreFamily a s F π hQ G relations i)
      (admissibleNatAt s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i D hD)
      (selectedDatum a s i D hD).val where
  embedding := P.embedding
  ref := P.ref
  r := P.r
  hCM := P.hCM
  hπ := hpiAt a s F π hQ han hN hcop H hm J O G relations i D hD P

end Reference

variable (refs : ∀ i D (hD : (withParamIndices a).admissible i D),
  Reference a s F π hQ hN hcop H hm J O G relations i D hD)

/-- The odd staged instance for (O.7), with the fixed parametrization
determining the quotient, `hπ`, the special-fibre Atkin equation and
the specialization of the cusp annihilation. -/
theorem oddStagedOfGoodRows
    (ha : ∀ i D (hD : (withParamIndices a).admissible i D),
      let row := actualRows s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations)
        (AtkinSign.actualRowFamily s hN hcop H F.signs hm J O (signedFamily a s F π hQ G relations)
          (hCuspAt (a := a) (s := s) (F := F) (π := π) (hQ := hQ) (hN := hN) (hcop := hcop)
            (J := J) (O := O) (G := G) (relations := relations) (cusps := cusps))
          (pointInputs a s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations)
            (fun i D hD => referenceComparisons a s F π hQ han hN hcop H hm J O G relations
              i D hD (refs i D hD)))) i D hD
      (2 : Coefficients hN (H 0) F.signs) ^ (withParamIndices a).Mθ i ∣
        row.weights.phase row.reference * ((withParamIndices a).aθ i D : Coefficients hN (H 0) F.signs) -
          Visibility.thetaCoeff
            (actualFamily s hN hcop H F.signs hm J O (fibreFamily a s F π hQ G relations) i).visibility
            ((m : ℤ) * D : ℤ))
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) a.f a.Lat a.κ (withParamIndices a).hstar L)
    (hsign : AdmissibleOddSign (withParamIndices a).toRCData) :
    Nonempty (OddStagedInstance (withParamIndices a)) :=
  oddStagedOfPinnedParamValues a s F hN hcop H hm J O (signedFamily a s F π hQ G relations)
    (fun i D hD => referenceComparisons a s F π hQ han hN hcop H hm J O G relations i D hD (refs i D hD))
    (hCuspAt (a := a) (s := s) (F := F) (π := π) (hQ := hQ) (hN := hN) (hcop := hcop)
      (J := J) (O := O) (G := G) (relations := relations) (cusps := cusps)) ha hL hsign


end ZInQ.Manuscript.RC.PMQuotient
