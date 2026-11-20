import ZInQKernel.Contrib.OneProof.RC.StageKummer.Assemble

/-! The integrator-facing family on the actual stage maps. The optional
coefficient reading concerns the theta side alone. -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual Visibility.ThetaStage

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ}
  (s : StageKummer.Setup I L)
  {O : Type} [CommRing O] {hN : 0 < StageKummer.level ℓ}
  (S : ∀ i, StageAt O (StageKummer.level ℓ) (W.Mθ i) hN (-W.hstar))
  (A : ∀ i D, W.admissible i D → DatumAt (S i) D (lamOf W.Mθ L I.selG s.ev i D))

/-- The positive integer filter can be read through the natural index of the
local weight and normalizer constructions. -/
def datumAtInt (i : ℕ) (D : ℤ) (hD : 0 < D)
    (row : DatumAt (S i) (D.toNat : ℤ) (lamOf W.Mθ L I.selG s.ev i (D.toNat : ℤ))) :
    DatumAt (S i) D (lamOf W.Mθ L I.selG s.ev i D) := by
  have h := Int.toNat_of_nonneg hD.le
  generalize (D.toNat : ℤ) = d at h row
  subst d
  exact row

variable
  (contract : ∀ i (n : ℤ), (2 : O) ^ W.Mθ i ∣ (n : O) → (2 : ℤ) ^ W.Mθ i ∣ n)
  (ha : ∀ i D (hD : W.admissible i D),
    (2 : O) ^ W.Mθ i ∣ (A i D hD).weights.phase (A i D hD).reference * (W.aθ i D : O) -
      thetaCoeff (S i).visibility ((((S i).weights.m : ℤ) * D : ℤ) : ℚ))

include contract ha in
/-- The actual comparison on the existing coefficient index, given its
independent reading at the chosen phase. -/
theorem thetaComparison :
    Odd.ThetaComparison W.Mθ W.aθ (lamOf W.Mθ L I.selG s.ev) W.admissible
      (StageKummer.level ℓ).primeFactors.card :=
  thetaComparison_actual W.Mθ S W.aθ (lamOf W.Mθ L I.selG s.ev) W.admissible A contract ha

/-- Use this wrapper at the existing `PreLeaves.odd_staged` field. The
comparison and witness both use `Setup.ev`, the actual family. -/
def oddStagedInstance
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
    (hsign : AdmissibleOddSign W.toRCData) : OddStagedInstance W :=
  StageKummer.toOddStagedInstanceOfReference s S A contract ha hL hsign

include A contract in
/-- If the caller is free to choose its integer representative, the raw
coefficient congruence supplies it at the original retained precision. -/
theorem thetaComparison_chosenRepresentative :
    Odd.ThetaComparison W.Mθ
      (fun i D => (Odd.c0 : ℤ) * 2 ^ (StageKummer.level ℓ).primeFactors.card *
        lamOf W.Mθ L I.selG s.ev i D)
      (lamOf W.Mθ L I.selG s.ev) W.admissible (StageKummer.level ℓ).primeFactors.card :=
  thetaComparison_actual W.Mθ S _ _ W.admissible A contract
    (fun i D hD => (A i D hD).representative)

end ZInQ.Manuscript.RC.O7Assemble
