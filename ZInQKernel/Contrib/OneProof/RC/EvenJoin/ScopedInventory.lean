import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped

/-! Two ingredients of a fixed-set inventory construction: gather the
fields of definition, and place the resulting seed coefficients in the
fixed integral ring before building the model lattice. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion ModularForm NumberField
open ThetaCoeff UpperHalfPlane Wiring IsDedekindDomain
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped ModularForm

/-- Once the individual fields of definition of the finitely many sources
are known, one number field contains all of them and the fixed phase field.
The completion and its embedding are separate from this algebraic step. -/
theorem finite_constituent_compositum {I : Type*} [Finite I]
    (F : IntermediateField ℚ ℂ) [NumberField F] (D : I → IntermediateField ℚ ℂ)
    [∀ i, NumberField (D i)] :
    ∃ E : IntermediateField ℚ ℂ, NumberField E ∧ F ≤ E ∧ ∀ i, D i ≤ E := by
  let E : IntermediateField ℚ ℂ := F ⊔ ⨆ i, D i
  let : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup _ _
  exact ⟨E, {}, le_sup_left,
    fun i => (le_iSup D i).trans le_sup_right⟩

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {X : Model P hS B}

/-- The computed inventory vector is already integral coefficientwise.
This comparison precedes the column and seed identities in a model. -/
theorem evenSeed_coeff_fixedRing {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
    (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (E : FixedPlaceExtension v X)
    (i : Fin 2) (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (Y : Inventory I J X.K (evenTypes W.S hS.1) N) (hm : movingLevel P U ∣ N)
    (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
    (κ : X.K →+* ℂ) (hκ : κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC)
    (hspan : SpansOverComplex Y κ) (n : ℕ) :
    (Y.toBasis hc).eval n
        (evenSeed hS i U hU hodd (E.source C₀) Y hm hc κ hκ hspan) =
      algebraMap X.O X.K (E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)) := by
  apply κ.injective
  rw [evenSeed_eval hS i U hU hodd (E.source C₀) Y hm hc κ hκ hspan,
    E.apply_ringMap]
  have h₀ := commonCoeff_place C₀ hS Subtype.val_injective i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  change _ = κ (E.fieldMap (algebraMap (FixedRing v) (FixedField v)
    (timesTheta (dividedCoeff (source_at_place C₀ hS Subtype.val_injective) i U.toList
      U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))) n)))
  rw [h₀, ← RingHom.comp_apply E.fieldMap C₀.eK, ← RingHom.comp_apply κ, hκ,
    commonCoeff_complex C₀ hS i U.toList n, joinedForm_coeff hS i U hU hodd n]

end ZInQ.Manuscript.RC.EvenJoin
