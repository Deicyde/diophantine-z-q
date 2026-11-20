import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Character
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Assembly
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Assemble

/-! The per-row join at the actual stage from the representative and local-factor readings. Geometry, the detector, the
chosen point lifts, and the level weights are shared by construction. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

/-- Transport equality of two signs through a change of label and an
Artin equivalence followed by its inverse. -/
theorem relabel_sign {X Y : Type*} (f g : X → ℤ) (e : X ≃ Y)
    {a b : X} (h : a = b) (hs : f a = g a) : f b = g (e.symm (e b)) := by
  subst b
  rw [e.symm_apply_apply]
  exact hs

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

/-- Read both factors in the actual stage's chosen frame. -/
theorem stageReadAt :
    TorusWeights.StageRead (actualStage s i hN hcop H w hm J G) (n : ℤ)
      (normFactors (StageKummer.stage_mod_four s i) hN H)
      (schwartzFactors (StageKummer.stage_mod_four s i) hN H w _
        (normFactors_unit (StageKummer.stage_mod_four s i) hN H)) :=
  ⟨stageNormRead (StageKummer.stage_mod_four s i) hN H hcop w,
    fun z x => stageSchwartzRead (StageKummer.stage_mod_four s i) hN H w _
      hcop (normFactors_unit (StageKummer.stage_mod_four s i) hN H) z x.val x.prop.2.2⟩

include A in
/-- The admissible selector field and the two local inputs specify the
actual orbit parameter, which is reused for the weights and the moves. -/
def orbitsAt
    (ι : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ)))
    (T : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ p, Nonempty (LocalTorusChart (O7Orbits.ActualOrder (actualStage s i hN hcop H w hm J G)) ι
        (referenceUnit _ A (selectedBasis s i hN hcop H w hm J G A t) ι)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) p))
    (R : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ b, HasLocalRealizations (actualStage s i hN hcop H w hm J G)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) b) :
    letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
    OrbitFibers (actualStage s i hN hcop H w hm J G).visibility
      (index (actualStage s i hN hcop H w hm J G) (n : ℤ))
      (StageKummer.level ℓ).primeFactors.card (ClassGroup (𝓞 (StageKummer.chosenDatum t).K)) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  orbitFibers_of_local _ A (supportBridgeAt s i hN hcop H w hm J G A)
    (partnerSymbol s i H) (selectedBasis s i hN hcop H w hm J G A t) ι T R

variable
    (ι : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ)))
    (T : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ p, Nonempty (LocalTorusChart (O7Orbits.ActualOrder (actualStage s i hN hcop H w hm J G)) ι
        (referenceUnit _ A (selectedBasis s i hN hcop H w hm J G A t) ι)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) p))
    (R : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ b, HasLocalRealizations (actualStage s i hN hcop H w hm J G)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J G A t) ι) b)

variable
    (P : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      TorusWeights.TorusParametrization (actualStage s i hN hcop H w hm J G) (n : ℤ)
        (selectedBasis s i hN hcop H w hm J G A t) (orbitsAt s i hN hcop H w hm J G A t ι T R))
    (J' : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      TorusWeights.TorusIdealRead P)

/-- Form the weight record over the actual Picard fibres. -/
def weightsAt : TorusWeights (actualStage s i hN hcop H w hm J G).visibility
    (orbitsAt s i hN hcop H w hm J G A t ι T R) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
  TorusWeights.actualWeights P J' (normFactors (StageKummer.stage_mod_four s i) hN H)
    (schwartzFactors (StageKummer.stage_mod_four s i) hN H w _
      (normFactors_unit (StageKummer.stage_mod_four s i) hN H))
    (stageReadAt s i hN hcop H w hm J G) (descentAt s i hN hcop H w hm J G A t)

variable
    (hSign : ∀ j : Fin (StageKummer.level ℓ).primeFactors.card,
      (w (levelPrime (StageKummer.level ℓ) j).val : ℤ) =
        G.atkinSign (levelPrime (StageKummer.level ℓ) j).val)
    (hCusp : ∀ j : Fin (StageKummer.level ℓ).primeFactors.card,
      L • (PMAdelic.geometry J G).cusp (levelPrime (StageKummer.level ℓ) j).val = 0)

/-- The normalizers operate on the same orbit and chosen lift as the weights. -/
def movesAt :
    Normalizers (actualStage s i hN hcop H w hm J G).G (StageKummer.detector s i) L
      (actualStage s i hN hcop H w hm J G).weights
      (actualStage s i hN hcop H w hm J G).u (actualStage s i hN hcop H w hm J G).hu
      (orbitsAt s i hN hcop H w hm J G A t ι T R) :=
  O7Normalizers.normalizers (StageKummer.stage_mod_four s i) hN hcop H w J G
    (StageKummer.detector s i) L (actualStage s i hN hcop H w hm J G).hu
    (requestedIndices A) (levelFilter A) (orbitsAt s i hN hcop H w hm J G A t ι T R)
    rfl hSign hCusp

/-- The class label for reduction is the Artin image of the very same
Picard label used in the norm character. -/
def artinAt :
    (supportAt s i hN hcop H w hm J G A t).classGroup ≃
      DatumGalois (StageKummer.chosenDatum t) :=
  letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; letI := (StageKummer.chosenDatum t).nz
  J'.pic.toEquiv.trans (ringClassArtinEquiv (CST.conductorOrder (StageKummer.chosenDatum t).K 1)).toEquiv

variable
    (ref : Orientations (StageKummer.level ℓ).primeFactors.card)
    (r : (supportAt s i hN hcop H w hm J G A t).classGroup → X.Point)
    (hs : stageTest s.q i (n : ℤ))
    (ht : I.selG (n : ℤ) = some t)
    (hχF : StageKummer.ArtinMatch (StageKummer.chosenDatum t)
      (artinAt s i hN hcop H w hm J G A t ι T R P J')
      (weightsAt s i hN hcop H w hm J G A t ι T R P J').character)
    (hCM : ∀ c, r c =
      (J.idealClasses (ThetaStage.zc (orbitsAt s i hN hcop H w hm J G A t ι T R).param
        (ref, c))).val)
    (hπ : ∀ c, (PMAdelic.geometricInput J G).specialize (r c) =
      StageKummer.reduceDatum s i t hs (conjugate (StageKummer.chosenDatum t)
        (artinAt s i hN hcop H w hm J G A t ι T R P J' c)))

set_option maxHeartbeats 2400000 in
/-- Assemble the actual reference congruence and the other four inputs at
one admissible discriminant. No comparison of total coefficients is used. -/
def datumAtOfIdealRead : DatumAt (actualStage s i hN hcop H w hm J G) (n : ℤ)
    (lamOf W.Mθ L I.selG s.ev i (n : ℤ)) :=
  StageKummer.datumAt s i t hs (PMAdelic.geometricInput J G)
    (actualStage s i hN hcop H w hm J G).weights hm
    (supportAt s i hN hcop H w hm J G A t)
    (orbitsAt s i hN hcop H w hm J G A t ι T R)
    (weightsAt s i hN hcop H w hm J G A t ι T R P J')
    (movesAt s i hN hcop H w hm J G A t ι T R hSign hCusp)
    ref (artinAt s i hN hcop H w hm J G A t ι T R P J')
    r hCM hπ ht hχF

end Row

end ZInQ.Manuscript.RC.O7Assemble
