import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedModel
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDeterminant
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped

/-! Instantiate the scoped carrier from the actual columns and their
z₀. The completion and its residue ideal both come from the chosen prime. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion IsDedekindDomain
open NumberField O12 PrintsArith ThetaCoeff TraceLimits UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped AdicCompletionExtension MatrixGroups

set_option quotPrecheck false

set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem fixedRing_continuousSMul {E : IntermediateField ℚ ℂ} [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) : ContinuousSMul (FixedRing w) (FixedField w) where
  continuous_smul := by
    change Continuous (fun x : FixedRing w × FixedField w => (x.1 : FixedField w) * x.2)
    exact (continuous_subtype_val.comp continuous_fst).mul continuous_snd

attribute [local instance] fixedRing_continuousSMul

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)] [NeZero (conductor W.S)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)
variable (hLi : OldNewIndependenceWeightTwo)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (H : D.sourceAttachments (hS := hS) hLi)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

local notation "τT" => evenTypes W.S hS.1
local notation "κK" => FixedField D.w
local notation "οO" => FixedRing D.w
local notation "μO" => IsLocalRing.maximalIdeal οO
local notation "b₀" => D.evenBasis hU hLi
local notation "z₀" => D.seed hU hLi C₀ hκ
local notation "ρ₀" => D.evenAttachment hU hLi H
local notation "i₀" => (Subtype.val_injective : Function.Injective (algebraMap οO κK))
local notation "h₀" => D.integral_diamonds hU C₀ hκ hLi hB hJ hodd

include htwo in
private theorem two_mem_extended : (2 : οO) ∈ μO := by
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  have hv : (2 : FixedRing v) ∈ IsLocalRing.maximalIdeal (FixedRing v) := by
    rw [← v.under_maximalIdeal_adicCompletionIntegers (K := F), Ideal.under_def, Ideal.mem_comap,
      map_ofNat] at htwo
    exact htwo
  have hmap : D.ringMap (2 : FixedRing v) = (2 : οO) := map_ofNat D.ringMap 2
  rw [← hmap]
  change (2 : FixedRing v) ∈ (μO).comap D.ringMap
  rw [show (μO).comap D.ringMap = IsLocalRing.maximalIdeal (FixedRing v) from
    v.comap_maximalIdeal_adicCompletionIntegersExtension F D.E D.w]
  exact hv

private theorem maximal_closed (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v) :
    IsClosed (IsLocalRing.maximalIdeal (FixedRing D.w) : Set (FixedRing D.w)) := by
  letI : Finite (𝓞 D.E ⧸ D.w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient D.w.ne_bot
  exact lattice_closed (IsLocalRing.maximalIdeal (FixedRing D.w)) (IsNoetherian.noetherian _)

include hU C₀ hκ hLi hB hJ hodd H horder htwo in
/-- The actual row model, formed from integral Hecke and diamond translates.
The only Galois input is the intrinsic attachment at each source. -/
def PlacedCuspLists.model (B : ℕ) : Σ X : Model P hS B, FourierData X := by
  letI : Finite (𝓞 D.E ⧸ D.w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient D.w.ne_bot
  let hm : (μO).IsMaximal := IsLocalRing.maximalIdeal.isMaximal οO
  let h2 : (2 : οO) ∈ μO := two_mem_extended D htwo
  let he : Topology.IsEmbedding (algebraMap οO κK) := Topology.IsEmbedding.subtypeVal
  let hfrob : ∀ q, (τT).Good q → IsFrobAt (chooseFrob frobeniusExists q) q :=
    fun _ hq => chooseFrob_spec frobeniusExists hq.1
  have htyp : IsTypeChar τT (typChar (conductor W.S)) :=
    isTypeChar_typeData _ (conductor_pos hS.1) _
  exact oneSeedModel b₀ z₀ ρ₀ i₀ h₀
    (exists_fixingSubgroup_le_ker_typChar _) htyp hm h2 (maximal_closed D) he hfrob
    (D.determinantData hU C₀ hκ hLi hB hJ hodd H hm h2 horder) rfl
    (oneSeed_twoTrace b₀ z₀ ρ₀ i₀ h₀ hfrob (maximal_closed D) he
      (D.fresh_coeff_mem hU C₀ hκ hLi hB hJ hodd h2))
    W.S (stationary_radicals hS) ((fixed_support hS).le) hS.2.1 _ _ B

local notation "M" => D.model hU C₀ hκ hLi hB hJ hodd H horder htwo

/-- The map of coefficient rings and the normalized valuation are induced
by extending the original fixed place. -/
def PlacedCuspLists.extension (B : ℕ) : FixedPlaceExtension v (M B).1 := by
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  exact {
    fieldMap := D.fieldMap
    finite := constituent_completion_finite v D.w
    val := constituentValuation v D.w
    complete := constituentValuation_complete v D.w
    normalized := constituentValuation_extends v D.w
    ringMap := D.ringMap
    commute := RingHom.ext (D.ringMap_agrees)
    integral := constituentValuation_integral v D.w
    maximal := constituentValuation_maximal v D.w }

theorem PlacedCuspLists.model_base (B : ℕ) :
    D.κ.comp ((D.extension hU C₀ hκ hLi hB hJ hodd H horder htwo B).fieldMap.comp
      (FinitePlace.embedding v)) = F.subtype :=
  RingHom.ext (D.fieldMap_complex)

theorem PlacedCuspLists.model_source (B : ℕ) :
    D.κ.comp ((D.extension hU C₀ hκ hLi hB hJ hodd H horder htwo B).fieldMap.comp C₀.eK) =
      C₀.eC := hκ

theorem PlacedCuspLists.model_maximal (B : ℕ) : (M B).1.m.IsMaximal :=
  IsLocalRing.maximalIdeal.isMaximal οO

theorem PlacedCuspLists.model_hecke (B : ℕ) : HeckeAt (M B).2 U := by
  intro q hq hqa
  let ops := oneOps b₀ z₀ ρ₀ (O := οO)
  let f := oneLatSeed b₀ (O := οO) z₀ U
  refine ⟨ops.diamond q f, fun n => ?_⟩
  have ht : (M B).1.tΛ ((M B).1.frob q) ((M B).1.F U) = ops.hecke q f := by
    apply Subtype.ext
    change tV (ρ₀).ρ (chooseFrob frobeniusExists q) f = (ops.hecke q f).val
    exact ops.trace_eq q hq hqa f
  rw [ht]
  exact oneCoeff_hecke b₀ z₀ ρ₀ i₀ h₀ q hq hqa n f

/-- The coordinate premise for the actual row, from the constructor's
column and z₀ identities. -/
theorem PlacedCuspLists.model_coordinates (B : ℕ) (n : ℕ) (hn : n ≠ 0) :
    D.κ (algebraMap (M B).1.O (M B).1.K ((M B).2.coeff n ((M B).1.F U))) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  rw [← (M B).2.expand_coeff ((M B).1.F U) ⟨n, hn⟩, (M B).1.expand_spec]
  change D.κ ((b₀).eval n (oneSeed z₀ U)) = _
  rw [oneSeed_same]
  exact D.seed_complex hU hLi C₀ hκ hodd n

end ZInQ.Manuscript.RC.EvenJoin
