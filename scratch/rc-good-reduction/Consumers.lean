import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Row
import ZInQKernel.Contrib.OneProof.RC.O7Residual.At

/-! Check the pointwise conclusion at the actual row's data. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.GoodReduction

open Wiring Stages Visibility O7Assemble O7Residual O7Actual O7Orbits
  PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

attribute [local irreducible] StageKummer.datumOnModel ringClassArtinEquiv

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
  (r : (supportAt s i hN hcop H w hm J G A t).classGroup → X.Point)

set_option maxHeartbeats 850000 in
set_option maxRecDepth 1600 in
example (h : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
    datumReduction (StageKummer.chosenDatum t) (StageKummer.place s i)
      (StageKummer.chosenDatumPlace s i t (show stageTest s.q i (n : ℤ) from A.detecting))
      (StageKummer.goodAt s i)
      (conjugate (StageKummer.chosenDatum t) (artinLabelAt s i hN hcop H w hm J G A t c))) :
    ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
      StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting)
        (conjugate (StageKummer.chosenDatum t) (artinLabelAt s i hN hcop H w hm J G A t c)) :=
  h

end ZInQ.Manuscript.RC.GoodReduction
