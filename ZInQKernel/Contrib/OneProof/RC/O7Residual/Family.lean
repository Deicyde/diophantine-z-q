import ZInQKernel.Contrib.OneProof.RC.O7Residual.At
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.ActualFamily

/-! Assemble the actual rows at integer admissible indices, and expose
the conditional output used by `PreLeaves.odd_staged`. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Residual

open O7Assemble O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

section Row

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : StageKummer.Setup I L)
  (i : ℕ) [Fact (s.q.stage i).p.Prime]
  [(ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic]

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : PMAdelic.CoarseFibre}
  (J : PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN hcop X)
  (G : PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap X)

variable {n : ℕ}
  (A : AdmissibleD (actualStage s i hN hcop H w hm J G) (n : ℤ))
  (t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ ((n : ℤ) * W.hstar) 1 W.hstar)

/-- The reference embedding, the actual selector value and the two
pointwise comparisons at the reference orientation and chosen place. -/
structure PointInputs where
  t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ ((n : ℤ) * W.hstar) 1 W.hstar
  embedding : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ))
  ref : Orientations (StageKummer.level ℓ).primeFactors.card
  r : (supportAt s i hN hcop H w hm J G A t).classGroup → X.Point
  ht : I.selG (n : ℤ) = some t
  hCM : ∀ c, r c =
    (J.idealClasses (Visibility.ThetaStage.zc
      (orbitsAt s i hN hcop H w hm J G A t embedding
        (chartAt s i hN hcop H w hm J G A t embedding)
        (realizationsAt s i hN hcop H w hm J G A t embedding)).param (ref, c))).val
  hπ : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
    StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting)
      (conjugate (StageKummer.chosenDatum t) (artinLabelAt s i hN hcop H w hm J G A t c))

end Row

section Family

attribute [local irreducible] StageKummer.datumOnModel ringClassArtinEquiv

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ}
  (s : StageKummer.Setup I L)

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (G : ∀ i, PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap (X i))

/-- The admissible integer index is positive and has the same odd filter
when read as a natural index. -/
theorem admissibleNatAt (i : ℕ) (D : ℤ) (hD : W.admissible i D) :
    AdmissibleD (actualStage s i hN (hcop i) (H i) w hm (J i) (G i)) (D.toNat : ℤ) := by
  have h := admissibleAt s i hN (hcop i) (H i) w hm (J i) (G i) hD
  rw [Int.toNat_of_nonneg h.positive.le]
  exact h

variable
  (hSign : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    (w (levelPrime (StageKummer.level ℓ) j).val : ℤ) =
      (G i).atkinSign (levelPrime (StageKummer.level ℓ) j).val)
  (hCusp : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    L • (PMAdelic.geometry (J i) (G i)).cusp (levelPrime (StageKummer.level ℓ) j).val = 0)
  (points : ∀ i D (hD : W.admissible i D),
    PointInputs s i hN (hcop i) (H i) w hm (J i) (G i)
      (admissibleNatAt s hN hcop H w hm J G i D hD))

set_option maxHeartbeats 450000 in
set_option maxRecDepth 1600 in
/-- Actual comparison rows at every admissible index, with no
coefficient reading. `actualRows` transports the result back to D. -/
def actualRowFamily (i : ℕ) (D : ℤ) (hD : W.admissible i D) :
    DatumAt (actualFamily s hN hcop H w hm J G i) (D.toNat : ℤ)
      (lamOf W.Mθ L I.selG s.ev i (D.toNat : ℤ)) := by
  change DatumAt (actualStage s i hN (hcop i) (H i) w hm (J i) (G i)) _ _
  obtain ⟨t, ι, ref, r, ht, hCM, hπ⟩ := points i D hD
  exact datumAtActual s i hN (hcop i) (H i) w hm (J i) (G i)
    (admissibleNatAt s hN hcop H w hm J G i D hD)
    t ι (hSign i) (hCusp i) ref r ht hCM hπ

variable (ha : ∀ i D (hD : W.admissible i D),
  let row := actualRows s hN hcop H w hm J G
    (actualRowFamily s hN hcop H w hm J G hSign hCusp points) i D hD
  (2 : Coefficients hN (H 0) w) ^ W.Mθ i ∣
    row.weights.phase row.reference * (W.aθ i D : Coefficients hN (H 0) w) -
      Visibility.thetaCoeff (actualFamily s hN hcop H w hm J G i).visibility
        ((m : ℤ) * D : ℤ))

include ha in
set_option maxHeartbeats 1400000 in
/-- Conditional discharge of the existing `PreLeaves.odd_staged` field.
The independent reading of the fixed coefficient `W.aθ` is unchanged. -/
theorem oddStagedActual
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
    (hsign : AdmissibleOddSign W.toRCData) : Nonempty (OddStagedInstance W) :=
  ⟨actualOddStagedInstance s hN hcop H w hm J G
    (actualRowFamily s hN hcop H w hm J G hSign hCusp points) ha hL hsign⟩

end Family

end ZInQ.Manuscript.RC.O7Residual
