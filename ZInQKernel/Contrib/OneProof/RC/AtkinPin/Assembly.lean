import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Sign
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Family
import ZInQKernel.Contrib.OneProof.RC.SelectorTotal.Assembly
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Reduction

/-! One newform sign in the selector, the actual theta stage and the special
fibre (tex 8505–8507, 9331–9341). Interface assembly is on-the-spot (c). -/

set_option autoImplicit false

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.RC.AtkinPin

/-- The identical form, with Tau Ceti's newness, character and eigenform data. -/
structure ConsumerNewform {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W)
    [NeZero (newformLevel (Ecurve ℓ))] where
  form : HeckeRing.GL2.Newform (newformLevel (Ecurve ℓ)) 2
  trivial : form.χ = 1
  eq_form : form.toCuspFormGamma0 trivial = I.f

/-- The existing shared modularity input suffices; no further newform
comparison is required. -/
def consumerNewform {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W)
    [NeZero (newformLevel (Ecurve ℓ))] (hM : PrintsAnalytic.ModularNewform) :
    ConsumerNewform I := by
  letI := I.hE
  let H := ElkikMD.curveNewform_eq_assemblyForm hM I.f I.hf
  exact ⟨H.choose, H.choose_spec.1.1, DFunLike.coe_injective
    ((H.choose.coe_toCuspFormGamma0 _).trans H.choose_spec.2.symm)⟩

/-- The integral equation in StageKummer has the same rational curve and level. -/
theorem stageLevel_eq (ℓ : ℕ) : StageKummer.level ℓ = newformLevel (Ecurve ℓ) :=
  congrArg newformLevel (EcurveZ_baseChange ℓ)

/-- The stage sign read from the consumer's newform at the full prime power. -/
def ConsumerNewform.signs {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    [NeZero (newformLevel (Ecurve ℓ))] (F : ConsumerNewform I) : ℕ → ℤˣ :=
  wNew F.form F.trivial

open O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose SelectorTotal

section Selector

variable {ℓ : ℕ} {W₀ : WData ℓ} (a : ParamInputs W₀) {L : ℕ}
  (s : StageKummer.Setup (genusInstance a) L)
  [NeZero (newformLevel (Ecurve ℓ))] (F : ConsumerNewform (genusInstance a))

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : ∀ i, (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : ∀ i, DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p)
  (hm : (m : ℤ) = -(withParamIndices a).hstar) {ap : ℕ → ℤ} {X : ℕ → PMAdelic.CoarseFibre}
  (J : ∀ i, PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i))
  (O : ∀ i, PMAdelic.OperatorComparison (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN (hcop i) (X i) (J i))
  (S : ∀ i, AtkinSign.SpecialFibreAtSigns (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap (X i) F.signs)

variable (comparisons : ∀ i D (hD : (withParamIndices a).admissible i D),
  PointComparisons s i hN (hcop i) (H i) F.signs hm (J i) (O i) (S i).toSpecialFibre
    (admissibleNatAt s hN hcop H F.signs hm J O (fun i => (S i).toSpecialFibre) i D hD)
    (selectedDatum a s i D hD).val)
  (hCusp : ∀ i (j : Fin (StageKummer.level ℓ).primeFactors.card),
    L • (PMAdelic.geometry (J i) (O i) (S i).toSpecialFibre).cusp
      (levelPrime (StageKummer.level ℓ) j).val = 0)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2000 in
/-- Use the total selector's point comparison and the AtkinSign constructor
with the same pinned sign in the coefficient ring, rows and geometry. The
remaining `ha` reads the fixed integer `aθ` on these very rows. -/
theorem oddStagedOfPinnedParamValues
    (ha : ∀ i D (hD : (withParamIndices a).admissible i D),
      let row := actualRows s hN hcop H F.signs hm J O (fun i => (S i).toSpecialFibre)
        (AtkinSign.actualRowFamily s hN hcop H F.signs hm J O S hCusp
          (pointInputs a s hN hcop H F.signs hm J O (fun i => (S i).toSpecialFibre) comparisons))
        i D hD
      (2 : Coefficients hN (H 0) F.signs) ^ (withParamIndices a).Mθ i ∣
        row.weights.phase row.reference *
            ((withParamIndices a).aθ i D : Coefficients hN (H 0) F.signs) -
          Visibility.thetaCoeff
            (actualFamily s hN hcop H F.signs hm J O (fun i => (S i).toSpecialFibre) i).visibility
            ((m : ℤ) * D : ℤ))
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) a.f a.Lat a.κ (withParamIndices a).hstar L)
    (hsign : AdmissibleOddSign (withParamIndices a).toRCData) :
    Nonempty (OddStagedInstance (withParamIndices a)) :=
  AtkinSign.oddStagedActual s hN hcop H F.signs hm J O S hCusp
    (pointInputs a s hN hcop H F.signs hm J O (fun i => (S i).toSpecialFibre) comparisons) ha hL hsign

end Selector


end ZInQ.Manuscript.RC.AtkinPin
