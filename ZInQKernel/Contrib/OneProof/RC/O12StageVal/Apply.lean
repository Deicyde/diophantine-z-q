import ZInQKernel.Contrib.OneProof.RC.O12StageVal.PM
import ZInQKernel.Contrib.OneProof.RC.O12StageVal.Stage
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Assembly
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddApMod

/-! Apply the unchanged finite-precision consumer to the stages of the skeleton.
The same stage index supplies both the actual theta coefficients and the intrinsic
odd symbol; the Galois realization and local inputs are explicit. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12StageVal
set_option maxHeartbeats 800000

open AddressGenuine PrintsArith TraceLimits ThetaCoeff ZInQ.Manuscript.RC.Odd O12 O12Theta Eichler Filter
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {ℓ i W Rb : ℕ} (D : RCData ℓ) (domain : ℕ → ℤ → Prop)

/-- App G's eventual choice for the skeleton's source and its minimum on the
intrinsic odd filter. The address support can impose more prime exclusions. -/
theorem integerDepth_of_data
    (hM : Tendsto D.Mθ (D.stages : Filter ℕ) atTop)
    (C : ℚ)
    (hF5 : ∀ j n, domain j n → ZInQ.Contrib.CloudB3RC53.AppGEndpoints.QLe
      (min (D.Mθ j : ℚ) (ZInQ.Contrib.CloudB3RC53.AppGEndpoints.omega n - C))
      (ZInQ.Manuscript.RC.vZ (D.aθ j n)))
    (hmin : IsLeast (ZInQ.Contrib.CloudB3RC53.AppGEndpoints.DepthSet D.stages D.Mθ
      (fun j n => ZInQ.Manuscript.RC.vZ (D.aθ j n)) domain) D.δo)
    (hR : 2 ≤ Rb) :
    ∀ᶠ j in (D.stages : Filter ℕ),
      IntegerDepth (D.Mθ j) W Rb D.δo (fun n => domain j n) (D.aθ j) := by
  simp only [← Wiring.odd_vZ_eq] at hF5 hmin
  exact integerDepth_of_min D.stages D.Mθ hM D.aθ domain C hF5 hmin hR

/-- The existing address reading uses the same intrinsic odd symbol, evaluated
at the product of the distinct primes. No equality of filters away from that
domain is used. -/
theorem rodd_eq_intrinsic {W₀ : Wiring.WData ℓ} (Q : LabelData W₀)
    {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) :
    Rodd W₀ Q i V = intrinsic (W₀.aθ i) W₀.δo (fun n => Q.oddAdmissible i n) V := by
  classical
  rw [intrinsic_read _ _ _ hV]
  unfold Rodd
  apply if_congr ?_ rfl rfl
  rw [Nat.cast_prod, Wiring.odd_vZ_eq, add_comm W₀.δo]

variable {a b : ℚ} {R : Order a b} {N ell : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic]
variable (G : PM.Geometry K R N Ebar (apo ℓ)) (d : PM.Evaluation K Ebar (D.Mθ i)) (mult : ℕ)
variable {O : Type} [CommRing O] (F : PMLocal O R (D.Mθ i) N ell)
variable (u : ClassSet R → ℤ) (hu : PM.IsLift G d mult u)

/-- Both divisions use the actual (O.4) series, with the elliptic coefficients
of the same curve used by the (O.12) constituent model. -/
theorem pmDivisions
    (C : O7Comparison (pmStage G d mult F) (fun n => domain i n) (D.aθ i))
    (depth : IntegerDepth (D.Mθ i) W Rb D.δo (fun n => domain i n) (D.aθ i))
    (hR : 2 ≤ Rb)
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 6 * (ℓ : ℤ) → p ∈ F.support)
    (sieve : ∀ p, p.Prime → p ∈ F.support → ∀ n, p ∣ n → (pmLift G d mult F u hu).aθ n = 0)
    (off : ∀ n : ℕ, Squarefree n → ¬ domain i n → (pmStage G d mult F).aθ n = 0) :
    Divisions (pmLift G d mult F u hu) D.δo W Rb (fun n => domain i n) :=
  divisions (pmLift G d mult F u hu) C depth hR
    (fun p hp => GlueSweep.Odd.ap_mod_four_curve (ℓ : ℤ) hp.1 (fun hd => hp.2 (hbad p hp.1 hd)))
    (pmLift_zero G d mult F u hu)
    (fun p hp hnot => sieve p hp (by classical exact not_not.mp (fun h => hnot ⟨hp, h⟩)))
    off

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {B : ℕ}
variable {X : GaloisConstituentModel T (intrinsic (D.aθ i) D.δo (fun n => domain i n))
  (apo ℓ) B χ}
variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]

/-- (O.12) at the valid odd stage, applied to the actual weighted series with
the intrinsic odd symbol. The arguments involving the common model are its
remaining realization, residue, type, Hecke, and local comparisons. -/
theorem inputs_of_pm (F : PMLocal X.O R (D.Mθ i) N ell) (A : FourierData X)
    (C : O7Comparison (pmStage G d mult F) (fun n => domain i n) (D.aθ i))
    (depth : IntegerDepth (D.Mθ i) W Rb D.δo (fun n => domain i n) (D.aθ i))
    (hR : 2 ≤ Rb) (hbudget : B ≤ W + 1)
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 6 * (ℓ : ℤ) → p ∈ F.support)
    (hcover : ∀ p ∈ F.support, p.Prime → p ∣ T.m)
    (sieve : ∀ p, p.Prime → p ∈ F.support → ∀ n, p ∣ n → (pmLift G d mult F u hu).aθ n = 0)
    (off : ∀ n : ℕ, Squarefree n → ¬ domain i n → (pmStage G d mult F).aθ n = 0)
    (hm : X.m.IsMaximal) (htyp : IsTypeChar T χ)
    (hexp : ∀ U (hU : Admissible (pmStage G d mult F) W U),
      (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B → ∀ n,
        A.coeff n (X.F U) = (pmLift G d mult F u hu).FourierF
          (pmDivisions D domain G d mult F u hu C depth hR hbad sieve off) hU n)
    {avoid : Finset ℕ} (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hhecke : A.FormwiseHecke) (localData : LocalInput A) : X.Inputs := by
  let E := pmLift G d mult F u hu
  let V := pmDivisions D domain G d mult F u hu C depth hR hbad sieve off
  have hgood : ∀ p, T.Good p → (pmStage G d mult F).Good p :=
    fun _ hp => good_of_support hcover hp
  exact inputs_at_precision A E V hgood hbudget rfl hm htyp
    (fun p hp => F.eta_order hp.1 (hgood p hp).2) hexp ops DF hDF hhecke
    (stageValuation E V C depth hbudget (fun _ _ _ => rfl)) localData

#print axioms integerDepth_of_data
#print axioms rodd_eq_intrinsic
#print axioms pmDivisions
#print axioms inputs_of_pm

end ZInQ.Manuscript.RC.O12StageVal
