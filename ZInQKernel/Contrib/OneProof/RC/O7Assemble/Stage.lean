import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Filter
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Character.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Character.Character
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Reference
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry

/-! The support uses the quadratic field of the actual selected datum. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

/-- The coefficient field of the chosen level characters is independent
of the detecting prime: the prime appears only in the proof of the
unit property of the prescribed parity. -/
theorem coefficients_eq {m N p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hN : 0 < N)
    (Hp : DiscriminantData m N p) (Hq : DiscriminantData m N q) (w : ℕ → ℤˣ) :
    Coefficients hN Hp w = Coefficients hN Hq w := by
  rfl

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

abbrev actualStage : StageAt (Coefficients hN H w) (StageKummer.level ℓ) (W.Mθ i) hN (-W.hstar) :=
  StageKummer.referenceStage s i (PMAdelic.geometricInput J G)
    (actualPmLocal (StageKummer.stage_mod_four s i) hN hcop H w) hm

/-- The admissibility predicate on the wiring gives the full support
filter on the actual stage, using the same prime and genus partner. -/
theorem admissibleAt {D : ℤ} (hD : W.admissible i D) :
    AdmissibleD (actualStage s i hN hcop H w hm J G) D := by
  have hprep : W.prepared D := (show W.prepared D ∧ stageTest s.q i D from
    (congrArg (fun V : WData ℓ => V.admissible i D) s.hstages.withStages_eq).mpr hD).1
  have hp := I.hprep D hprep
  have hg := I.hgp
  have hs := s.stageTest_of_admissible hD
  have hN_eq : CST.newformLevel (Ecurve ℓ) = StageKummer.level ℓ := by
    rw [StageKummer.level, EcurveZ_baseChange]
  have hm' : -((actualStage s i hN hcop H w hm J G).weights.m : ℤ) = W.hstar := by
    change -(m : ℤ) = W.hstar
    rw [hm, neg_neg]
  exact admissible_of_prepared hN_eq (hm'.symm ▸ hp) (hm'.symm ▸ hg) hs

variable {n : ℕ}
  (A : AdmissibleD (actualStage s i hN hcop H w hm J G) (n : ℤ))
  (t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ ((n : ℤ) * W.hstar) 1 W.hstar)

include A in
/-- Read the support from the finished theta constructor on the full filter. -/
theorem supportBridgeAt : SupportBridge (actualStage s i hN hcop H w hm J G) (n : ℤ) := by
  intro z x hx hn
  refine actualFilteredSupport (StageKummer.stage_mod_four s i) hN H w z n _
    (requestedIndices A) (levelFilter A) x hx ?_
  exact_mod_cast hn

theorem discAt :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    discr (StageKummer.chosenDatum t).K = disc (actualStage s i hN hcop H w hm J G) (n : ℤ) := by
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  change discr (StageKummer.chosenDatum t).K = (n : ℤ) * -(m : ℤ)
  rw [hm, neg_neg]
  exact (StageKummer.chosenDatum t).disc

/-- The integral basis of the same field used by the selected datum. -/
abbrev selectedBasis :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    QuadraticBasis (StageKummer.chosenDatum t).K (disc (actualStage s i hN hcop H w hm J G) (n : ℤ)) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  O7Character.quadraticBasis (StageKummer.chosenDatum t).finrank_two (discAt s i hN hcop H w hm J G t)
    (PicardFibers.AdmissibleD.disc_neg A) (by
      have h8 : ((n : ℤ) * -(m : ℤ)) % 8 = 1 := A.mod_eight
      change ((n : ℤ) * -(m : ℤ)) % 4 = 1
      omega)

include A in
/-- The conventional trivial genus character at one and the proved
conductor-one norm descent elsewhere, for the actual selected datum. -/
theorem descentAt :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    NormCharacterDescent (StageKummer.chosenDatum t).K (-(m : ℤ)) := by
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  exact TorusWeights.descent_of_filter (oddFilter A) (StageKummer.chosenDatum t).finrank_two
    (discAt s i hN hcop H w hm J G t)
    (fun _ => O7Character.normCharacterDescent (StageKummer.chosenDatum t).finrank_two
      (discAt s i hN hcop H w hm J G t) (PicardFibers.AdmissibleD.disc_neg A) A.mod_eight)

include H in
theorem partnerSymbol :
    legendreSym (s.q.stage i).p (-(m : ℤ)) = -1 := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact H.inert

/-- The selected row determines the quadratic field of the integral support. -/
def supportAt : IntegralSupport (actualStage s i hN hcop H w hm J G) (n : ℤ) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  O7Orbits.integralSupport _ (supportBridgeAt s i hN hcop H w hm J G A) (StageKummer.chosenDatum t).K
    (selectedBasis s i hN hcop H w hm J G A t) (PicardFibers.AdmissibleD.disc_neg A) A.mod_eight

end Row

end ZInQ.Manuscript.RC.O7Assemble
