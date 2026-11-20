import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! The integral division happens at the chosen prime above two. Only the
constituent space and its field of realization are chosen at a tested set.
The prime and the two completion types are the components of the fixed
coefficient place (tex 9638–9654). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion ModularForm NumberField O12
open ThetaCoeff UpperHalfPlane Wiring IsDedekindDomain
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped ModularForm NNReal

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F]

abbrev FixedField (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
abbrev FixedRing (v : HeightOneSpectrum (𝓞 F)) := ↥(v.adicCompletionIntegers F)

/-- A finite complete extension at the fixed place, with the absolute value
on its field normalized by restriction to the base. The two membership
conditions refer to the actual coefficient ring and reduction ideal of the model. -/
structure FixedPlaceExtension (v : HeightOneSpectrum (𝓞 F)) (X : Model P hS B) where
  fieldMap : FixedField v →+* X.K
  finite : letI := fieldMap.toAlgebra; FiniteDimensional (FixedField v) X.K
  val : Valuation X.K ℝ≥0
  complete : @CompleteSpace X.K (Valued.mk' val).toUniformSpace
  normalized : ∀ x : FixedField v, val (fieldMap x) = ‖x‖₊
  ringMap : FixedRing v →+* X.O
  commute : (algebraMap X.O X.K).comp ringMap =
    fieldMap.comp (algebraMap (FixedRing v) (FixedField v))
  integral : ∀ y : X.K, (∃ z : X.O, algebraMap X.O X.K z = y) ↔ val y ≤ 1
  maximal : ∀ z : X.O, z ∈ X.m ↔ val (algebraMap X.O X.K z) < 1

variable {v : HeightOneSpectrum (𝓞 F)} {X : Model P hS B}
variable (E : FixedPlaceExtension v X)

theorem FixedPlaceExtension.apply_ringMap (x : FixedRing v) :
    algebraMap X.O X.K (E.ringMap x) =
      E.fieldMap (algebraMap (FixedRing v) (FixedField v) x) :=
  DFunLike.congr_fun E.commute x

/-- The divisibility threshold on the extension is the norm of the actual
integer power of two at the chosen place, including for ramified extensions. -/
theorem FixedPlaceExtension.two_pow_dvd_iff (A : FourierData X) (a : ℕ) (z : X.O) :
    (2 : X.O) ^ a ∣ z ↔
      E.val (algebraMap X.O X.K z) ≤ ‖(2 : FixedField v)‖₊ ^ a := by
  have hv : E.val ((2 : X.K) ^ a) = ‖(2 : FixedField v)‖₊ ^ a := by
    rw [← map_ofNat E.fieldMap, ← map_pow, E.normalized, nnnorm_pow]
  let : CharZero X.K := charZero_of_injective_ringHom E.fieldMap.injective
  have hn : (2 : X.K) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, map_ofNat, map_mul, ← hv]
    exact mul_le_of_le_one_right' ((E.integral _).mp ⟨y, rfl⟩)
  · intro h
    have he : E.val (algebraMap X.O X.K z / (2 : X.K) ^ a) ≤ 1 := by
      rw [map_div₀, div_le_one ((E.val.ne_zero_iff.mpr hn).bot_lt), hv]
      exact h
    obtain ⟨y, hy⟩ := (E.integral _).mpr he
    refine ⟨y, A.integral_inclusion ?_⟩
    rw [map_mul, map_pow, map_ofNat, hy, mul_div_cancel₀ _ hn]

/-- For a coefficient coming from the fixed ring, reduction is tested
using its fixed norm, independent of the extension or its uniformizer. -/
theorem FixedPlaceExtension.reduce_eq_zero_iff (x : FixedRing v) :
    Ideal.Quotient.mk X.m (E.ringMap x) = 0 ↔
      ‖algebraMap (FixedRing v) (FixedField v) x‖₊ < 1 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, E.maximal, E.apply_ringMap, E.normalized]

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))

/-- Change only the receiving ring and field of the fixed source. -/
def FixedPlaceExtension.source : SourceAtPlace P X.O X.K where
  K₀ := C₀.K₀
  eC := C₀.eC
  eK := E.fieldMap.comp C₀.eK
  c := C₀.c
  η₀ := C₀.η₀
  k := C₀.k
  a n := E.ringMap (C₀.a n)
  «η» n := E.ringMap (C₀.η n)
  complex_coeff := C₀.complex_coeff
  complex_eta := C₀.complex_eta
  integral_coeff n := by
    rw [E.apply_ringMap, C₀.integral_coeff, map_mul, map_zpow₀, map_ofNat]
    rfl
  integral_eta n := by
    rw [E.apply_ringMap, C₀.integral_eta]
    rfl
  phase_lift D hD := by
    obtain ⟨z, ζ, hz, hζ⟩ := C₀.phase_lift D hD
    exact ⟨z, E.ringMap ζ, hz, (E.apply_ringMap ζ).trans (congrArg E.fieldMap hζ)⟩
  padicInt := E.ringMap.comp C₀.padicInt
  padic := E.fieldMap.comp C₀.padic
  padic_agree x :=
    (E.apply_ringMap (C₀.padicInt x)).trans (congrArg E.fieldMap (C₀.padic_agree x))

omit [NeZero (conductor W.S)] in
/-- The divided coefficient was already integral at the fixed place,
before considering any realization of a weight-two form. -/
def fixedH (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) : ℕ → FixedRing v :=
  dividedCoeff (source_at_place C₀ hS Subtype.val_injective) i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))

omit [NeZero (conductor W.S)] in
/-- The numerator is divisible by the required integer power in the
fixed coefficient ring itself (tex 9640–9643). -/
theorem fixed_numerator_dvd (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) (n : ℕ) :
    (2 : FixedRing v) ^ (P.δ + C₀.k + (U.card : ℤ) + 1).toNat ∣
      rawNumerator (evenTypes W.S hS.1).Good C₀.η C₀.a i U.toList n := by
  simpa only [Finset.length_toList] using
    (rawNumerator_dvd (source_at_place C₀ hS Subtype.val_injective) i U.toList
      U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n)

variable [CharZero X.K] (A : FourierData X)
variable (i : Fin 2) (U : Finset ℕ)
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (κ : X.K →+* ℂ) (hκ : κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC)

omit [CharZero X.K] in
include hκ in
/-- The preceding characteristic-zero seed construction is used within a
single model, by comparing the columns and the seed of this tested set. -/
theorem coordinate_match_of_seed_scoped {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
    (Y : Inventory I J X.K (evenTypes W.S hS.1) N) (hm : movingLevel P U ∣ N)
    (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
    (hspan : SpansOverComplex Y κ) (ι : (I → X.K) →ₗ[X.K] (X.I → X.K))
    (hcolumn : ∀ w n, X.coefK (ι w) (A.index n) = (Y.toBasis hc).eval n.val w)
    (hseed : (X.F U).val = ι (evenSeed hS i U hU hodd (E.source C₀) Y hm hc κ hκ hspan)) :
    ∀ n, n ≠ 0 → κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n :=
  coordinate_match_of_seed hS A (E.source C₀) i U hU hodd Y hm hc κ hκ hspan ι hcolumn hseed

/-- The two images of the fixed divided series coincide before reduction. -/
theorem map_fixed_theta (n : ℕ) :
    timesTheta (evenH hS A (E.source C₀) i U) n =
      E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) := by
  apply A.integral_inclusion
  rw [E.apply_ringMap]
  have hA := commonCoeff_place (E.source C₀) hS A.integral_inclusion i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  have h₀ := commonCoeff_place C₀ hS Subtype.val_injective i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  have he : evenH hS A (E.source C₀) i U =
      dividedCoeff (source_at_place (E.source C₀) hS A.integral_inclusion) i U.toList
        U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) := by
    funext m
    unfold evenH
    exact dite_eq_left hU
  rw [he]
  exact hA.trans (congrArg E.fieldMap h₀).symm

include hκ in
/-- The realized coefficients are the images of the series divided at the
fixed place. Thus the extension does not perform any extra division. -/
theorem evenExpansion_joined_scoped
    (hcoord : ∀ n, n ≠ 0 → κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n) :
    ∀ n, n ≠ 0 → A.coeff n (X.F U) =
      E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) := fun n hn =>
  (evenExpansion_joined hS A (E.source C₀) i U hU hodd κ hκ hcoord n hn).trans
    (map_fixed_theta E C₀ A i U hU n)

section Budget

/-- The good Hecke formula only on the seed at this set. -/
def HeckeAt (A : FourierData X) (U : Finset ℕ) : Prop :=
  ∀ q, (evenTypes W.S hS.1).Good q → q ∉ U → ∃ diamondF : X.Λ, ∀ n,
    A.coeff n (X.tΛ (X.frob q) (X.F U)) =
      A.coeff (q * n) (X.F U) +
        if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0

/-- The local characteristic-zero data at the members of this set. -/
def LocalAt (A : FourierData X) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) : Prop :=
  ∀ q (hqU : q ∈ U) (Q : LocalPair q),
    letI : Fact q.Prime := ⟨(hU q hqU).1⟩
    Nonempty (O12Local.Stage A U Q (hU q hqU).1.ne_zero)

/-- One fixed source and coefficient place, with one realization for each tested set.
The carrier model can still use the old type; no assertion identifies any off-set seed in it
with an actual modular form. -/
def BudgetRealizationScoped (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
    (i : Fin 2) (B : ℕ) : Prop :=
  (2 : 𝓞 F) ∈ v.asIdeal ∧
  (∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C₀.η p ^ (2 ^ t) = 1) ∧
  ∀ (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p), U.card + 1 ≤ B →
    ∃ (X : Model P hS B) (A : FourierData X) (E : FixedPlaceExtension v X)
      (κ : X.K →+* ℂ),
      κ.comp (E.fieldMap.comp (FinitePlace.embedding v)) = F.subtype ∧
      κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC ∧ X.m.IsMaximal ∧
      HeckeAt A U ∧ LocalAt A U hU ∧
      ∀ n, n ≠ 0 → A.coeff n (X.F U) =
        E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)

/-- Produce the scoped budget interface from a separate coordinate match
for each set. The operator and local hypotheses are tested only at that set. -/
theorem budgetRealization_of_joined_scoped
    (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (i : Fin 2)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (htwo : (2 : 𝓞 F) ∈ v.asIdeal)
    (hphase : ∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C₀.η p ^ (2 ^ t) = 1)
    (hdata : ∀ (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p),
      U.card + 1 ≤ B →
      ∃ (X : Model P hS B) (A : FourierData X) (E : FixedPlaceExtension v X)
        (κ : X.K →+* ℂ),
        κ.comp (E.fieldMap.comp (FinitePlace.embedding v)) = F.subtype ∧
        κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC ∧ X.m.IsMaximal ∧
        HeckeAt A U ∧ LocalAt A U hU ∧
        ∀ n, n ≠ 0 → κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
          (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n) :
    BudgetRealizationScoped (hS := hS) C₀ i B := by
  refine ⟨htwo, hphase, fun U hU hB => ?_⟩
  obtain ⟨X, A, E, κ, hF, hκ, hm, hHecke, hlocal, hcoord⟩ := hdata U hU hB
  let : CharZero X.K := charZero_of_injective_ringHom E.fieldMap.injective
  exact ⟨X, A, E, κ, hF, hκ, hm, hHecke, hlocal,
    evenExpansion_joined_scoped E C₀ A i U hU hodd κ hκ hcoord⟩

end Budget

end ZInQ.Manuscript.RC.EvenJoin
