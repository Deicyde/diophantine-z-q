import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Family

/-! The comparison and its odd wiring at the actual stages. -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Stages
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual PMGeometry ThetaClose Visibility.ThetaStage

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ}
  (s : StageKummer.Setup I L)

instance stagePrime (i : ℕ) : Fact (s.q.stage i).p.Prime := ⟨(s.q.stage i).prime⟩

instance stageElliptic (i : ℕ) : (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic := by
  letI := s.eE; letI := s.eA
  exact StageIdent.selectedCurveOn_elliptic (EcurveZ ℓ) (EcurveZ_baseChange ℓ)
    rfl rfl s.dat s.w s.hQw s.q i

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (O : ∀ i, PMAdelic.OperatorComparison (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i) (J i))
  (G : ∀ i, PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap (X i))

/-- The coefficient ring is fixed while the theta order and point detector
vary with the detecting prime. -/
abbrev actualFamily (i : ℕ) :
    StageAt (Coefficients hN (H 0) w) (StageKummer.level ℓ) (W.Mθ i) hN (-W.hstar) :=
  actualStage s i hN (hcop i) (H i) w hm (J i) (O i) (G i)

variable (rows : ∀ i D, W.admissible i D →
  DatumAt (actualFamily s hN hcop H w hm J O G i) (D.toNat : ℤ)
    (lamOf W.Mθ L I.selG s.ev i (D.toNat : ℤ)))

/-- Transport the positive natural index of each actual row to the wiring index. -/
abbrev actualRows (i : ℕ) (D : ℤ) (hD : W.admissible i D) :
    DatumAt (actualFamily s hN hcop H w hm J O G i) D (lamOf W.Mθ L I.selG s.ev i D) :=
  datumAtInt s (actualFamily s hN hcop H w hm J O G) i D
    (admissibleAt s i hN (hcop i) (H i) w hm (J i) (O i) (G i) hD).positive (rows i D hD)

variable (ha : ∀ i D (hD : W.admissible i D),
  (2 : Coefficients hN (H 0) w) ^ W.Mθ i ∣
    (actualRows s hN hcop H w hm J O G rows i D hD).weights.phase
      (actualRows s hN hcop H w hm J O G rows i D hD).reference *
        (W.aθ i D : Coefficients hN (H 0) w) -
      thetaCoeff (actualFamily s hN hcop H w hm J O G i).visibility ((m : ℤ) * D : ℤ))

include ha in
/-- The actual theta comparison using the independent reading of `W.aθ`. -/
theorem actualThetaComparison :
    Odd.ThetaComparison W.Mθ W.aθ (lamOf W.Mθ L I.selG s.ev) W.admissible
      (StageKummer.level ℓ).primeFactors.card :=
  thetaComparison s (actualFamily s hN hcop H w hm J O G) (actualRows s hN hcop H w hm J O G rows)
    (fun i => ring_two (coefficientPlace hN (H 0) w) (coefficientPlace_over_two hN (H 0) w)
      (W.Mθ i)) ha

/-- Wrapper for the existing `PreLeaves.odd_staged` field at the actual stages. -/
def actualOddStagedInstance
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
    (hsign : AdmissibleOddSign W.toRCData) : OddStagedInstance W :=
  oddStagedInstance s (actualFamily s hN hcop H w hm J O G) (actualRows s hN hcop H w hm J O G rows)
    (fun i => ring_two (coefficientPlace hN (H 0) w) (coefficientPlace_over_two hN (H 0) w)
      (W.Mθ i)) ha hL hsign

end ZInQ.Manuscript.RC.O7Assemble
