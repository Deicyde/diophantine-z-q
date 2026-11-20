import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Join
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Ideals
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Parametrization

/-! The per-row join at the actual stage. Geometry, the detector, the
chosen point lifts, and the level weights are shared by construction. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

theorem partner_ne_zero {m N ell : ℕ} [Fact ell.Prime] (H : DiscriminantData m N ell) : m ≠ 0 := by
  have := H.odd
  omega

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

variable
    (ι : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ)))
    (T : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ p, Nonempty (LocalTorusChart (O7Orbits.ActualOrder (actualStage s i hN hcop H w hm J G)) ι
        (referenceUnit _ A (selectedBasis s i hN hcop H w hm J G A t) ι)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) p))
    (R : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ b, HasLocalRealizations (actualStage s i hN hcop H w hm J G)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) b)

variable (hr : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  OrbitRead (actualStage s i hN hcop H w hm J G) A (supportBridgeAt s i hN hcop H w hm J G A)
    (partnerSymbol s i H) (selectedBasis s i hN hcop H w hm J G A t) ι T R
    (normalizedIdele m (partner_ne_zero H)))

abbrev parametrizationAt :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    TorusWeights.TorusParametrization _ (n : ℤ) (selectedBasis s i hN hcop H w hm J G A t)
      (orbitsAt s i hN hcop H w hm J G A t ι T R) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  torusParametrization _ A (supportBridgeAt s i hN hcop H w hm J G A)
    (partnerSymbol s i H) (selectedBasis s i hN hcop H w hm J G A t) ι T R
    (normalizedIdele m (partner_ne_zero H)) (normalized_class m (partner_ne_zero H)) hr

variable (hnorm : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  ∀ (c : ClassGroup (𝓞 (StageKummer.chosenDatum t).K)) (p : Adelic.Prime),
    let P := parametrizationAt s i hN hcop H w hm J G A t ι T R hr
    Padic.valuation (TorusWeights.localNrd p ((P.embedIdeles (P.idele c)).val p) : ℚ_[p.val]) =
      ((Ideal.absNorm (coprimeIdeal m (partner_ne_zero H) c).val).factorization p.val : ℤ))

/-- Read the ideal and norm on the chosen representatives; the only local
input beyond the chart is the reduced norm valuation on these representatives. -/
def idealReadAt :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    TorusWeights.TorusIdealRead (parametrizationAt s i hN hcop H w hm J G A t ι T R hr) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  normalizedIdealRead m (partner_ne_zero H) _ rfl (fun _ => rfl)
    (torusParametrization_block_one _ A (supportBridgeAt s i hN hcop H w hm J G A)
      (partnerSymbol s i H) (selectedBasis s i hN hcop H w hm J G A t) ι T R _ _ hr) hnorm

variable
    (hSign : ∀ j : Fin (StageKummer.level ℓ).primeFactors.card,
      (w (levelPrime (StageKummer.level ℓ) j).val : ℤ) =
        G.atkinSign (levelPrime (StageKummer.level ℓ) j).val)
    (hCusp : ∀ j : Fin (StageKummer.level ℓ).primeFactors.card,
      L • (PMAdelic.geometry J G).cusp (levelPrime (StageKummer.level ℓ) j).val = 0)

variable
    (ref : Orientations (StageKummer.level ℓ).primeFactors.card)
    (r : (supportAt s i hN hcop H w hm J G A t).classGroup → X.Point)
    (ht : I.selG (n : ℤ) = some t)
    (hχF : StageKummer.ArtinMatch (StageKummer.chosenDatum t)
      (artinAt s i hN hcop H w hm J G A t ι T R
        (parametrizationAt s i hN hcop H w hm J G A t ι T R hr)
        (idealReadAt s i hN hcop H w hm J G A t ι T R hr hnorm))
      (weightsAt s i hN hcop H w hm J G A t ι T R
        (parametrizationAt s i hN hcop H w hm J G A t ι T R hr)
        (idealReadAt s i hN hcop H w hm J G A t ι T R hr hnorm)).character)
    (hCM : ∀ c, r c =
      (J.idealClasses (ThetaStage.zc (orbitsAt s i hN hcop H w hm J G A t ι T R).param
        (ref, c))).val)
    (hπ : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
      StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting) (conjugate (StageKummer.chosenDatum t)
        (artinAt s i hN hcop H w hm J G A t ι T R
          (parametrizationAt s i hN hcop H w hm J G A t ι T R hr)
          (idealReadAt s i hN hcop H w hm J G A t ι T R hr hnorm) c)))

set_option maxHeartbeats 1800000 in
/-- Assemble one actual admissible row. The reduced norm valuation is
stated only on the normalized representatives used for this row. -/
def datumAt : DatumAt (actualStage s i hN hcop H w hm J G) (n : ℤ)
    (lamOf W.Mθ L I.selG s.ev i (n : ℤ)) :=
  datumAtOfIdealRead s i hN hcop H w hm J G A t ι T R
    (parametrizationAt s i hN hcop H w hm J G A t ι T R hr)
    (idealReadAt s i hN hcop H w hm J G A t ι T R hr hnorm)
    hSign hCusp ref r A.detecting ht hχF hCM hπ

end Row

end ZInQ.Manuscript.RC.O7Assemble
