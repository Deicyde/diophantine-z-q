import ZInQKernel.Contrib.OneProof.RC.StageIdent.Detector
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Filter

/-! Apply the finite-precision consumer at the selected Appendix F/G stage.
The level, residue curve, multiplier, and detector are fixed before the local
theta data are supplied. The existing (O.12) model inputs remain explicit. -/

noncomputable section

open WeierstrassCurve TauCeti
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.WitnessSpec ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.StageIdent

open AddressGenuine TraceLimits ThetaCoeff ZInQ.Manuscript.RC.Odd O12 O12Theta O12StageVal Eichler
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000

variable {ℓ : ℕ} (W : WData ℓ) [(Ecurve ℓ).IsElliptic]
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (Ecurve ℓ)) :
    Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {Dw : ℤ}
  (dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * W.hstar) 1 W.hstar)
  {L : ℕ} (w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L)
  [(qtwist (Ecurve ℓ) (Dw : ℚ)).IsElliptic] {a : ℕ} {S : Finset ℕ}
  {F₀ : IntermediateField ℚ Qbar} {σ : GalQ} {Qw : GeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ))}
  (hQw : Qw = rationalGeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ)) w.rational)
  (q : StageSequence (ActualAt (qtwist (Ecurve ℓ) (Dw : ℚ)) (Ecurve ℓ) Qw F₀ σ Dw W.hstar)
    (a + 1) S)
  (hσ : tateRep (Ecurve ℓ) 2 (σ * σ) = 1)
  (b : TateMod (qtwist (Ecurve ℓ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist (Ecurve ℓ) (Dw : ℚ)) 2 σ t) = b t)
  (hs : withStages W q W.prepared = W)
  (i : ℕ) [(reducedEquation (EcurveZ ℓ) (q.stage i).p).IsElliptic]

/-- The order's numeric level is the newform level of the integral model's
generic fibre, which is the same curve used in the skeleton. -/
theorem level_eq (ℓ : ℕ) :
    CST.newformLevel ((EcurveZ ℓ)⁄ℚ) = CST.newformLevel (Ecurve ℓ) :=
  congrArg CST.newformLevel (EcurveZ_baseChange ℓ)

/-- Choose the detector of the actual sequence at the precision in `W`. -/
abbrev detectorAt :=
  selectedEvaluationOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ b hb
    (congrArg (fun V : WData ℓ => V.Mθ) hs.symm) i

/-- The evaluation part of `actualForStages` is Appendix F's detector. The
heterogeneous equality records the dependent presentation of the fixed group
in the transported genus maps. -/
theorem detectorAt_lam (emb : StageMap.DatumEmbeddings (Ecurve ℓ) f Lat κ W.hstar) :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    HEq (PM.lam (detectorAt W dat w hQw q hσ b hb hs i))
      ((StageMap.actualForStages W dat w hQw q hσ emb b hs).eval i) :=
  selectedEvaluationOn_lam (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ b hb
    (congrArg (fun V : WData ℓ => V.Mθ) hs.symm) i emb

variable [Fact (q.stage i).p.Prime] {qa qb : ℚ} {R : Order qa qb}
  (G : PM.Geometry (residueAt (selectedFrobenius q i).property.1) R
    (CST.newformLevel (Ecurve ℓ)) (reducedEquation (EcurveZ ℓ) (q.stage i).p) (apo ℓ))

/-- The order has the level of the skeleton curve, and the prime and extracted
index of the weighted source are the selected prime and the genus modulus.
The local constructor supplies the field `F.m` directly. -/
theorem pmStage_parameters {O : Type} [CommRing O]
    (F : PMLocal O R (W.Mθ i) (CST.newformLevel (Ecurve ℓ)) (q.stage i).p)
    (hm : F.m = W.hstar.natAbs) :
    IsEichler (q.stage i).p (CST.newformLevel (Ecurve ℓ)) R ∧
    (pmStage G (detectorAt W dat w hQw q hσ b hb hs i) L F).ℓ₀ =
      (q.stage i).p ∧
    (pmStage G (detectorAt W dat w hQw q hσ b hb hs i) L F).m =
      W.hstar.natAbs :=
  ⟨G.eichler, rfl, hm⟩

/-- The finite weight on each ideal class uses the same detector before
taking its image in the stage coefficient ring. -/
theorem pmStage_weight {O : Type} [CommRing O]
    (F : PMLocal O R (W.Mθ i) (CST.newformLevel (Ecurve ℓ)) (q.stage i).p)
    (z : ClassSet R) :
    (pmStage G (detectorAt W dat w hQw q hσ b hb hs i) L F).P z =
      PM.stageCast O (W.Mθ i) ((PM.lam (detectorAt W dat w hQw q hσ b hb hs i)) (L • G.pi z)) :=
  rfl

variable (Q : LabelData W) (unit : Finset ℕ)
  (havoid : Q.m.primeFactors ⊆ S)
  (hfixed : Q.m₁.primeFactors ⊆ W.S) (hprime : ∀ p ∈ W.S, p.Prime)
  (hprep : W.prepared = fun D => positivePrepared unit D ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ D)

variable {χ : GalQ →* Multiplicative Q.L₁} {budget : ℕ}
  {X : GaloisConstituentModel ((labelsAtStages Q q unit hs havoid hfixed hprime hprep).T₁ i)
    (intrinsic (W.aθ i) W.δo (fun n => sourceFilter q unit Q.m₁.primeFactors i n))
    (apo ℓ) budget χ}

local instance : CommRing X.O := X.instO
local instance : Field X.K := X.instK
local instance : Algebra X.O X.K := X.instAlg

variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]

/-- At the selected stage, discharge the support and budget arguments of
`inputs_of_pm`. The same intrinsic filter is used in the comparison, depth,
support, and symbol. The least representatives are one permitted lift. -/
theorem inputs_of_selected
    (F : PMLocal X.O R (W.Mθ i) (CST.newformLevel (Ecurve ℓ)) (q.stage i).p)
    (hmIndex : F.m = W.hstar.natAbs)
    (hS : F.support = insert (q.stage i).p Q.m₁.primeFactors)
    (A : FourierData X) :
    let D := W.toRCData
    let domain := sourceFilter q unit Q.m₁.primeFactors
    let d := detectorAt W dat w hQw q hσ b hb hs i
    let Cₛ := pmStage G d L F
    let E := pmValLift G d L F
    let hbad := bad_mem_support Q q i hS
    ∀ (C : O7Comparison Cₛ (fun n => domain i n) (D.aθ i))
      (depth : IntegerDepth (D.Mθ i) (budget - 1) 2 D.δo (fun n => domain i n) (D.aθ i))
      (sieve : ∀ p, p.Prime → p ∈ F.support → ∀ n, p ∣ n → E.aθ n = 0)
      (off : ∀ n : ℕ, Squarefree n → ¬ domain i n → Cₛ.aθ n = 0),
      X.m.IsMaximal → IsTypeChar ((labelsAtStages Q q unit hs havoid hfixed hprime hprep).T₁ i) χ →
      (∀ U (hU : Admissible Cₛ (budget - 1) U),
        (∀ p ∈ U, ((labelsAtStages Q q unit hs havoid hfixed hprime hprep).T₁ i).Good p) →
        U.card + 1 ≤ budget → ∀ n, A.coeff n (X.F U) =
          E.FourierF (pmDivisions D domain G d L F (PM.valLift G d L)
            (PM.isLift_valLift G d L) C depth (reading_budget budget).2 hbad sieve off) hU n) →
      ∀ {avoid : Finset ℕ}
        (ops : GoodOperators ((labelsAtStages Q q unit hs havoid hfixed hprime hprep).T₁ i)
          avoid X.frob X.ρ X.Λ)
        (DF : ∀ U, DeterminantFourierData ops X.m (X.F U)),
        (∀ U, (DF U).coeff = A.coeff) →
        A.FormwiseHecke → LocalInput A →
        (IsEichler (q.stage i).p (CST.newformLevel (Ecurve ℓ)) R ∧
          Cₛ.ℓ₀ = (q.stage i).p ∧ Cₛ.m = W.hstar.natAbs) ∧
        sourceFilter q unit F.support i =
          (labelsAtStages Q q unit hs havoid hfixed hprime hprep).oddAdmissible i ∧
        X.Inputs := by
  dsimp only
  intro C depth sieve off hm htyp hexp avoid ops DF hDF hhecke localData
  have hcover : ∀ p ∈ F.support, p.Prime →
      p ∣ ((labelsAtStages Q q unit hs havoid hfixed hprime hprep).T₁ i).m := by
    intro p hp _
    rw [LabelData.T₁_m]
    exact support_dvd_type Q q i hS p hp
  refine ⟨pmStage_parameters W dat w hQw q hσ b hb hs i G F hmIndex,
    sourceFilter_eq Q q unit i hS, ?_⟩
  exact inputs_of_pm W.toRCData (sourceFilter q unit Q.m₁.primeFactors)
    G (detectorAt W dat w hQw q hσ b hb hs i) L _ (PM.isLift_valLift G _ L)
    F A C depth (reading_budget budget).2 (reading_budget budget).1
    (bad_mem_support Q q i hS) hcover sieve off hm htyp hexp ops DF hDF hhecke localData

#print axioms level_eq
#print axioms detectorAt_lam
#print axioms pmStage_parameters
#print axioms pmStage_weight
#print axioms inputs_of_selected

end ZInQ.Manuscript.RC.StageIdent
