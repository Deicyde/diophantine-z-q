import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Family

/-! The actual (O.7) family with one choice of Atkin–Lehner signs. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.AtkinSign

open O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ}
  (s : StageKummer.Setup I L)
variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (S : ∀ i, SpecialFibreAtSigns (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap (X i) w)

variable
  (hCusp : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    L • (PMAdelic.geometry (J i) (S i).toSpecialFibre).cusp
      (levelPrime (StageKummer.level ℓ) j).val = 0)
  (points : ∀ i D (hD : W.admissible i D),
    PointInputs s i hN (hcop i) (H i) w hm (J i) (S i).toSpecialFibre
      (admissibleNatAt s hN hcop H w hm J (fun i => (S i).toSpecialFibre) i D hD))

set_option maxHeartbeats 450000 in
set_option maxRecDepth 1600 in
/-- On-the-spot (c): the existing actual row at each admissible index.
The sign equality follows by definition for the geometry built from `S`. -/
def actualRowFamily (i : ℕ) (D : ℤ) (hD : W.admissible i D) :
    DatumAt (actualFamily s hN hcop H w hm J (fun i => (S i).toSpecialFibre) i) (D.toNat : ℤ)
      (lamOf W.Mθ L I.selG s.ev i (D.toNat : ℤ)) :=
  O7Residual.actualRowFamily s hN hcop H w hm J (fun i => (S i).toSpecialFibre)
    (fun _ _ => rfl) hCusp points i D hD

variable (ha : ∀ i D (hD : W.admissible i D),
  let row := actualRows s hN hcop H w hm J (fun i => (S i).toSpecialFibre)
    (actualRowFamily s hN hcop H w hm J S hCusp points) i D hD
  (2 : Coefficients hN (H 0) w) ^ W.Mθ i ∣
    row.weights.phase row.reference * (W.aθ i D : Coefficients hN (H 0) w) -
      Visibility.thetaCoeff (actualFamily s hN hcop H w hm J (fun i => (S i).toSpecialFibre) i).visibility
        ((m : ℤ) * D : ℤ))

include ha in
set_option maxHeartbeats 1400000 in
set_option maxRecDepth 1600 in
/-- On-the-spot (c): the actual odd staged instance with the same
independent coefficient reading and point inputs as the existing wrapper. -/
theorem oddStagedActual
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
    (hsign : AdmissibleOddSign W.toRCData) : Nonempty (OddStagedInstance W) :=
  O7Residual.oddStagedActual s hN hcop H w hm J (fun i => (S i).toSpecialFibre)
    (fun _ _ => rfl) hCusp points ha hL hsign


end ZInQ.Manuscript.RC.AtkinSign
