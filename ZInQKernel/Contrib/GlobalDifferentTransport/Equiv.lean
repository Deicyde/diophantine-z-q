/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Selected valuation/completion-isomorphism proofs adapted to Mathlib v4.35.0
from TauCeti revision a6027b1d24fcb935c53bd5b50d11b40991cda418:
Topology/Algebra/Valued/WithVal.lean, RingTheory/DedekindDomain/AdicValuation/Transport.lean,
and the small value-group embedding lemma in Algebra/GroupWithZero/Range.lean.
The ideal valuation comparison uses Mathlib's multiplicity-map equivalence.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Completion
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Valuation-compatible isomorphisms and their completions

A ring isomorphism carrying a prime to a prime preserves its normalized adic
valuation. A valuation-compatible fraction-field isomorphism extends to the
corresponding completions, preserving the valuation and the global embedding.
No local degree formula or decomposition-group cardinality is assumed.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZeroTopology
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

namespace GlobalDifferentTransport

section IdealValuation

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing R'] [IsDedekindDomain R']

/-- An isomorphism carrying a prime to a prime preserves its integral adic valuation. -/
theorem intValuation_ringEquiv (e : R ≃+* R')
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have her : e r ≠ 0 := by simp [hr]
  let E : Ideal R ≃* Ideal R' :=
    { e.idealComapOrderIso.symm.toEquiv with map_mul' := Ideal.map_mul e }
  rw [w.intValuation_eq_exp_neg_multiplicity her,
    v.intValuation_eq_exp_neg_multiplicity hr,
    hvw, ← Set.image_singleton, ← Ideal.map_span]
  congr 2
  have hm : multiplicity (E v.asIdeal) (E (Ideal.span {r})) =
      multiplicity v.asIdeal (Ideal.span {r}) := multiplicity_map_eq E
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) hm

variable {K K' : Type*} [Field K] [Field K']
  [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']

/-- The induced fraction-field isomorphism preserves the normalized adic valuation. -/
theorem valuation_ringEquivOfRingEquiv (e : R ≃+* R')
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (x : K) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e x) = v.valuation K x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, map_div₀,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap e a,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap e b,
    valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_ringEquiv e hvw a, intValuation_ringEquiv e hvw b]

end IdealValuation

section WithVal

variable {A C : Type*} [Ring A] [Ring C] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  {q : Valuation A Γ} {q' : Valuation C Γ}

@[simp]
private theorem valueGroup_embedding_coe
    {M N : Type*} [MonoidWithZero M] [GroupWithZero N]
    {f : M →*₀ N} (x : valueGroup f) :
    embedding (x : ValueGroup₀ f) = ((x : Nˣ) : N) := by
  simp [embedding_apply]

/-- A valuation-preserving ring isomorphism is uniformly continuous on the valued type synonyms. -/
theorem withVal_uniformContinuous_congr (σ : A ≃+* C)
    (hσ : ∀ x, q' (σ x) = q x) : UniformContinuous (WithVal.congr q q' σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  have hγ : WithVal.valueGroupOrderIso₀ q' γ.1 ≠ 0 := by simp
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (WithVal.valueGroupOrderIso₀ q' γ.1).zero_or_exists_mk.resolve_left hγ
  have hva : q (σ.symm a) ≠ 0 := by simpa [← hσ]
  have hvb : q (σ.symm b) ≠ 0 := by simpa [← hσ]
  let δ : q.ValueGroup₀ := valueGroup.mk (q : A →*₀ Γ) (σ.symm a) (σ.symm b) hva hvb
  have hδ : δ ≠ 0 := by simp [δ]
  let γ' : (Valued.v (R := WithVal q)).ValueGroup₀ˣ :=
    Units.mk0 ((WithVal.valueGroupOrderIso₀ q).symm δ) (by simp [hδ])
  refine ⟨γ', trivial, ?_⟩
  intro x hx
  rw [Set.mem_ofPred_eq] at hx ⊢
  apply (WithVal.strictMono_valueGroupOrderIso₀ q').lt_iff_lt.mp
  change (WithVal.valueGroupOrderIso₀ q') ((WithVal.valuation q').restrict _) < _
  rw [WithVal.valueGroupOrderIso₀_restrict, hab, Valuation.restrict_lt_iff_lt_embedding]
  have hx' := (WithVal.strictMono_valueGroupOrderIso₀ q).lt_iff_lt.mpr hx
  change (WithVal.valueGroupOrderIso₀ q) ((WithVal.valuation q).restrict x) < _ at hx'
  rw [WithVal.valueGroupOrderIso₀_restrict, Units.val_mk0, OrderMonoidIso.apply_symm_apply,
    Valuation.restrict_lt_iff_lt_embedding] at hx'
  have haeq : q' a = q (σ.symm a) := by rw [← hσ, RingEquiv.apply_symm_apply]
  have hbeq : q' b = q (σ.symm b) := by rw [← hσ, RingEquiv.apply_symm_apply]
  simpa [δ, WithVal.congr_apply, hσ, haeq, hbeq] using hx'

/-- The isomorphism of valuation completions induced by a valuation-compatible ring isomorphism. -/
def valuationCompletionRingEquiv (σ : A ≃+* C) (hσ : ∀ x, q' (σ x) = q x) :
    q.Completion ≃+* q'.Completion :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr q q' σ)
    (withVal_uniformContinuous_congr σ hσ).continuous
    (withVal_uniformContinuous_congr σ.symm
      (fun y ↦ by rw [← hσ, RingEquiv.apply_symm_apply])).continuous

/-- The valuation-completion isomorphism is the extension map on valued type synonyms. -/
theorem valuationCompletionRingEquiv_apply (σ : A ≃+* C)
    (hσ : ∀ x, q' (σ x) = q x) (x : q.Completion) :
    valuationCompletionRingEquiv σ hσ x = UniformSpace.Completion.map (WithVal.congr q q' σ) x :=
  UniformSpace.Completion.mapRingEquiv_apply _ _ _ x

/-- The induced isomorphism agrees with the original ring isomorphism on the dense image. -/
theorem valuationCompletionRingEquiv_coe (σ : A ≃+* C)
    (hσ : ∀ x, q' (σ x) = q x) (x : A) :
    valuationCompletionRingEquiv σ hσ (x : q.Completion) = (σ x : q'.Completion) := by
  rw [valuationCompletionRingEquiv_apply,
    UniformSpace.Completion.map_coe (withVal_uniformContinuous_congr σ hσ),
    WithVal.congr_apply, WithVal.ofVal_toVal]

/-- The induced isomorphism is continuous. -/
theorem continuous_valuationCompletionRingEquiv (σ : A ≃+* C)
    (hσ : ∀ x, q' (σ x) = q x) : Continuous (valuationCompletionRingEquiv σ hσ) :=
  UniformSpace.Completion.continuous_map.congr
    fun x ↦ (valuationCompletionRingEquiv_apply σ hσ x).symm

end WithVal

section Completion

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing R'] [IsDedekindDomain R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K]
  [Algebra R' K'] [IsFractionRing R' K']
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum R')
  (σ : K ≃+* K') (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x)

/-- The canonical ring isomorphism of adic completions induced by a valuation-compatible
isomorphism of the original fraction fields. -/
def adicCompletionRingEquiv : v.adicCompletion K ≃+* w.adicCompletion K' :=
  (adicCompletion.equiv K v).trans <|
    (valuationCompletionRingEquiv σ hσ).trans (adicCompletion.equiv K' w).symm

/-- The underlying uniform-space completion map of the isomorphism. -/
theorem toCompletion_adicCompletionRingEquiv (x : v.adicCompletion K) :
    (adicCompletionRingEquiv v w σ hσ x).toCompletion =
      valuationCompletionRingEquiv σ hσ x.toCompletion := by
  rw [adicCompletionRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    adicCompletion.equiv_apply, ← adicCompletion.equiv_apply, RingEquiv.apply_symm_apply]

/-- The adic-completion isomorphism agrees with the original field isomorphism. -/
theorem adicCompletionRingEquiv_algebraMap (x : K) :
    adicCompletionRingEquiv v w σ hσ (algebraMap K (v.adicCompletion K) x) =
      algebraMap K' (w.adicCompletion K') (σ x) := by
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionRingEquiv]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    adicCompletion.coe_toCompletion, valuationCompletionRingEquiv_coe]

/-- Continuity of the adic-completion isomorphism. -/
theorem continuous_adicCompletionRingEquiv : Continuous (adicCompletionRingEquiv v w σ hσ) :=
  (adicCompletion.continuous_ofCompletion K' w).comp
    ((continuous_valuationCompletionRingEquiv σ hσ).comp
      (adicCompletion.continuous_toCompletion K v))

/-- A continuous homomorphism agreeing on the original field is this canonical isomorphism. -/
theorem eq_adicCompletionRingEquiv_of_continuous
    {f : v.adicCompletion K →+* w.adicCompletion K'} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap K' (w.adicCompletion K') (σ x)) :
    f = (adicCompletionRingEquiv v w σ hσ).toRingHom :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_adicCompletionRingEquiv v w σ hσ) (funext fun x ↦ by
      rw [Function.comp_apply, Function.comp_apply, hfK x,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        adicCompletionRingEquiv_algebraMap])

/-- The adic-completion isomorphism preserves the completed normalized valuation. -/
theorem valued_adicCompletionRingEquiv (x : v.adicCompletion K) :
    Valued.v (adicCompletionRingEquiv v w σ hσ x) = Valued.v x := by
  rw [← adicCompletion.valued_toCompletion_apply,
    toCompletion_adicCompletionRingEquiv, valuationCompletionRingEquiv_apply]
  have hsurj : Function.Surjective (Valued.v : (v.valuation K).Completion → _) :=
    Valued.valuedCompletion_surjective_iff.mpr (.of_comp (v.valuation_surjective K))
  have hsurj' : Function.Surjective (Valued.v : (w.valuation K').Completion → _) :=
    Valued.valuedCompletion_surjective_iff.mpr (.of_comp (w.valuation_surjective K'))
  have heq : (fun z : (v.valuation K).Completion ↦
      Valued.v (UniformSpace.Completion.map (WithVal.congr (v.valuation K) (w.valuation K') σ) z)) =
      Valued.v := by
    apply UniformSpace.Completion.ext
    · exact (Valued.continuous_valuation_of_surjective hsurj').comp
        UniformSpace.Completion.continuous_map
    · exact Valued.continuous_valuation_of_surjective hsurj
    intro a
    rw [UniformSpace.Completion.map_coe (withVal_uniformContinuous_congr σ hσ),
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, WithVal.congr_apply]
    change w.valuation K' (σ a.ofVal) = v.valuation K a.ofVal
    exact hσ a.ofVal
  rw [congrFun heq]
  exact adicCompletion.valued_toCompletion_apply K v x

end Completion

end GlobalDifferentTransport
