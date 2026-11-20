import ZInQKernel.Contrib.OneProof.RC.O7Assemble.At
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Orbit
import ZInQKernel.Contrib.OneProof.RC.O7Residual.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Artin

/-! The actual (O.7) row with its local and arithmetic inputs
constructed at the selected field. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Residual

open O7Assemble O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

section Row

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

variable
    (ι : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ)))

/-- The torus chart at the selected field uses the reference root and
affine generator of the orbit assembly definitionally. -/
abbrev chartAt :=
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  LocalTorus.localTorusChart _ A (selectedBasis s i hN hcop H w hm J G A t) ι

/-- All orientation tuples have local realizations at the same generator. -/
abbrev realizationsAt :=
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  LocalTorus.hasLocalRealizations _ A (partnerSymbol s i H)
    (selectedBasis s i hN hcop H w hm J G A t) ι

set_option maxHeartbeats 1400000 in
/-- The actual Picard parameters use the normalized class ideles. -/
theorem orbitReadAt :
    letI := (StageKummer.chosenDatum t).field
    letI := (StageKummer.chosenDatum t).nf
    OrbitRead _ A (supportBridgeAt s i hN hcop H w hm J G A) (partnerSymbol s i H)
      (selectedBasis s i hN hcop H w hm J G A t) ι
      (chartAt s i hN hcop H w hm J G A t ι) (realizationsAt s i hN hcop H w hm J G A t ι)
      (normalizedIdele m (partner_ne_zero H)) :=
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  orbitRead _ A (supportBridgeAt s i hN hcop H w hm J G A) (partnerSymbol s i H)
    (selectedBasis s i hN hcop H w hm J G A t) ι _ _ _
    (normalized_class m (partner_ne_zero H))

/-- The Artin label for the ordinary ideal class, independent of local
bases, norm valuations and the coefficient ring. -/
abbrev artinLabelAt :
    (supportAt s i hN hcop H w hm J G A t).classGroup ≃
      DatumGalois (StageKummer.chosenDatum t) :=
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  letI := (StageKummer.chosenDatum t).nz
  (picOne (F := (StageKummer.chosenDatum t).K)).toEquiv.trans (ringClassArtinEquiv
    (CST.conductorOrder (StageKummer.chosenDatum t).K 1)).toEquiv
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
    (hCM : ∀ c, r c =
      (J.idealClasses (Visibility.ThetaStage.zc
        (orbitsAt s i hN hcop H w hm J G A t ι
          (chartAt s i hN hcop H w hm J G A t ι)
          (realizationsAt s i hN hcop H w hm J G A t ι)).param (ref, c))).val)
    (hπ : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
      StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting)
        (conjugate (StageKummer.chosenDatum t) (artinLabelAt s i hN hcop H w hm J G A t c)))

set_option maxHeartbeats 850000 in
set_option maxRecDepth 1600 in
/-- All five fields of one actual admissible row. The only additional
row hypotheses beyond the fixed signs and cusp identities are the
selector and the pointwise CM identifications. -/
def datumAtActual : DatumAt (actualStage s i hN hcop H w hm J G) (n : ℤ)
    (lamOf W.Mθ L I.selG s.ev i (n : ℤ)) := by
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  let S := actualStage s i hN hcop H w hm J G
  let Q := selectedBasis s i hN hcop H w hm J G A t
  let T := chartAt s i hN hcop H w hm J G A t ι
  let R := realizationsAt s i hN hcop H w hm J G A t ι
  let hr := orbitReadAt s i hN hcop H w hm J G A t ι
  let z := tupleBase S A (supportBridgeAt s i hN hcop H w hm J G A) Q ι R (fun _ => false)
  let P := parametrizationAt s i hN hcop H w hm J G A t ι T R hr
  have hn (c : ClassGroup (𝓞 (StageKummer.chosenDatum t).K)) (p : Adelic.Prime) :
      Padic.valuation (TorusWeights.localNrd p ((P.embedIdeles (P.idele c)).val p) :
        ℚ_[p.val]) = ((Ideal.absNorm (coprimeIdeal m (partner_ne_zero H) c).val).factorization
        p.val : ℤ) :=
    normalized_norm_valuation S.mod_four hN Q ι (referenceUnit_sphere S A Q ι).1
      T z.val z.prop m (partner_ne_zero H) c p
  let J' := idealReadAt s i hN hcop H w hm J G A t ι T R hr hn
  have hlabel :
      artinAt s i hN hcop H w hm J G A t ι T R P J' = artinLabelAt s i hN hcop H w hm J G A t := by
    rfl
  have hπ' (c : (supportAt s i hN hcop H w hm J G A t).classGroup) :
      (PMAdelic.geometricInput J G).specialize (r c) =
        StageKummer.reduceDatum s i t (show stageTest s.q i (n : ℤ) from A.detecting)
          (conjugate (StageKummer.chosenDatum t) (artinAt s i hN hcop H w hm J G A t ι T R P J' c)) := by
    rw [hlabel]
    exact hπ c
  have hχ := artinMatchAt s i hN hcop H w hm J G A t ι T R P J'
  exact O7Assemble.datumAt s i hN hcop H w hm J G A t ι T R hr hn
    hSign hCusp ref r ht hχ hCM hπ'

end Row

end ZInQ.Manuscript.RC.O7Residual
