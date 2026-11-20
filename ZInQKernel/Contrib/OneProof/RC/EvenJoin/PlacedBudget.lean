import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedModel
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalLocal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointConsumer

/-! Feed separately realized rows to the joint deletion consumer. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget EvenExpansion IsDedekindDomain NumberField O12
open O12Local PrintsArith Symbols ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option maxHeartbeats 2500000

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

/-- Only the local data on the actual cuspidal coordinates: the attached
representations at the added prime and the Whittaker comparison for their
local sum. -/
def CuspidalLocalAt {B : ℕ} {X : Model P hS B} (A : FourierData X) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) : Prop :=
  ∀ q (hqU : q ∈ U) (Q : LocalPair q),
    letI : Fact q.Prime := ⟨(hU q hqU).1⟩
    ∃ C : CuspidalData X Q, SupportedOn C.active (X.F U : X.I → X.K) ∧
      Nonempty (WhittakerComparison q (hU q hqU).1.ne_zero
        {z | SupportedOn C.active z} C.up (fun n z => X.coefK z (A.index n)))

theorem localAt_of_cuspidal {B : ℕ} {X : Model P hS B} (A : FourierData X) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) (H : CuspidalLocalAt A U hU) :
    LocalAt A U hU := by
  intro q hqU Q
  letI : Fact q.Prime := ⟨(hU q hqU).1⟩
  obtain ⟨C, hF, ⟨hW⟩⟩ := H q hqU Q
  exact ⟨cuspidalStage A U (hU q hqU).1.ne_zero C hF hW⟩

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (j : C₀.K₀ →+* F)
variable (hK : (FinitePlace.embedding v).comp j = C₀.eK) (hC : F.subtype.comp j = C₀.eC)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (hLi : OldNewIndependenceWeightTwo)

/-- One may choose the actual constituent lists and a place containing
the necessary local data, separately at each set. The only requests on
that choice are the intrinsic and the added-prime Galois inputs. -/
def PlacedGaloisInput (B : ℕ) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) : Prop :=
  letI : NeZero (movingLevel P U) := ⟨movingLevel_ne (P := P) (hS := hS) hU⟩
  ∃ (A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b) (evenBlockSeries P hS i b))
    (hB : IsMovingCharacter P U (A none).χ)
    (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
    (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
    (H : D.sourceAttachments (hS := hS) hLi),
    CuspidalLocalAt
      (D.model hU C₀ (D.fieldMap_source C₀ j hK hC) hLi hB hJ hodd H horder htwo B).2 U hU

theorem budgetRealization_of_placed (B : ℕ)
    (H : ∀ U hU, U.card + 1 ≤ B → PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hLi B U hU) :
    BudgetRealizationScoped (hS := hS) C₀ i B := by
  refine budgetRealization_of_joined_scoped C₀ i hodd htwo
    (fun p hp => eta_phase_of_character C₀ hS Subtype.val_injective horder hp) ?_
  intro U hU hcap
  letI : NeZero (movingLevel P U) := ⟨movingLevel_ne (P := P) (hS := hS) hU⟩
  obtain ⟨A, hB, hJ, D, att, hlocal⟩ := H U hU hcap
  let hκ := D.fieldMap_source C₀ j hK hC
  let M := D.model hU C₀ hκ hLi hB hJ hodd att horder htwo B
  let E := D.extension hU C₀ hκ hLi hB hJ hodd att horder htwo B
  exact ⟨M.1, M.2, E, D.κ, D.model_base hU C₀ hκ hLi hB hJ hodd att horder htwo B,
    D.model_source hU C₀ hκ hLi hB hJ hodd att horder htwo B,
    D.model_maximal hU C₀ hκ hLi hB hJ hodd att horder htwo B,
    D.model_hecke hU C₀ hκ hLi hB hJ hodd att horder htwo B,
    localAt_of_cuspidal M.2 U hU hlocal,
    D.model_coordinates hU C₀ hκ hLi hB hJ hodd att horder htwo B⟩

/-- The even rules and unit seed, with the actual coordinate comparison and
the joint deletion reading supplied. -/
theorem rules_and_seed_of_placed_joint
    (H : ∀ B U hU, U.card + 1 ≤ B →
      PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hLi B U hU) :
    CoefficientRules (evenSign W.S) (P.symbol hS) ∧
      ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ :=
  rules_and_seed_of_joined_joint C₀ i (fun B =>
    budgetRealization_of_placed C₀ j hK hC htwo hodd horder hLi B (H B))

end ZInQ.Manuscript.RC.EvenJoin
