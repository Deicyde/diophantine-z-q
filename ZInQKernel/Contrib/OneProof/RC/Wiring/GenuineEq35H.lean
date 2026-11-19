import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPK
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Pad

/-!
**Theorem 5.3: the (3.5) leaf with homology-level switching data**

Proposition `ex:limits-uniform-lower-bound` (tex 4909–5202) at the ring instances of Proposition
`ex:sec7-genus-lower` (tex 2418–2446), in the text's quantifier order and with the text's size bound
(5.1) (round 9's `Eq35InputsGenuineABounded`, `GenuineEq35Pad.lean`).

**The obstruction removed.** The regularity conjunct of `Eq35InputsGenuineABounded` is
`RegularityInputsGPK`, whose switching data `GenuineSwitchDataPK` take their steps from batch 3's
model-step bundles; these demand finite-dimensional cochain modules at the source of every switch
(`fG`), so over the actual genuine complexes (`C¹_cont` infinite-dimensional) no switch step can be
formed and the actual family witnesses the regularity part only when `s(𝔭) = 1`.
`Eq35InputsGenuineABoundedH W` is the same leaf with `RegularityInputsHPK` in place of
`RegularityInputsGPK`: the switching data `HomologySwitchDataPK` (`GenuineSwitchHPK.lean`) take the
homology-level steps of the RC53 group, which ask only for finiteness of cohomology. All other
conjuncts are verbatim (the data before `A`, (4.6), and for every `A` the outer model family with
sizes at most the cap of (5.1), genuine two-term models, the coordinate clause and the outer
switching data; the outer models are related to some genuine Galois Selmer data by homotopy
equivalences, `IsGenuineInstanceModel`, not tied to the instance; their switch steps
`OuterSwitchStep` carry an existential Selmer-level datum `X : SelmerNonquadStep` with cochain
finiteness `fG`, `fL`, `fF`, `fS`, not tied to the genuine complexes and met by finite models;
unchanged from the cochain-level leaf).

PROVED:
* `eq35Target_of_inputsAH`: (3.5) for each `A` from the new leaf (RC16's
  `exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`, as `eq35Target_of_inputsA`, with the
  regularity through `RegularityInputsHPK.toS`);
* `eq55_of_inputsAH`: (5.5) through batch 3's `uniform_lower_bound_of_genuine`;
* the comparison `Eq35InputsGenuineABounded.toH` (old ⇒ new, by `regularity_GPK_to_HPK`) and
  `Eq35InputsGenuineA.toH`;
* the degenerate satisfiability `eq35InputsGenuineABoundedH_of_not_prepared`.

Non-vacuity of the switching structure with fibres whose global cochains are infinite-dimensional,
over which the old data are impossible and the new data exist: `GenuineSwitchHNonVacuity.lean`.

**What remains.** The configuration families and the homotopy equivalences `model c` of
`HomologySwitchDataPK` are existential: they are not tied to the text's finite free models of the
address's complexes. The intended source of the models is lane RC31's `exists_gradedModel`
(`RC/Limits/GradedFiniteFree.lean`, Lemma `ex:limits-inner-limit`, tex 4391–4451; the homotopy
equivalence is `GRetract.homotopyEquiv`, `RC/Limits/GradedModel.lean`). The identification of the
genuine derivative conditions with the quasi switch sides and the GLUE of the step bundles remain as
in `GenuineSteps.lean`. The outer model family is existential as well (`IsGenuineInstanceModel` does
not tie the genuine Galois Selmer data to the instance).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with homology-level switching data** (Proposition
`ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of Proposition
`ex:sec7-genus-lower`, tex 2418–2446): round 9's `Eq35InputsGenuineABounded W` with the regularity
conjunct `RegularityInputsHPK` (homology-level switch steps, tex 4976–5194) in place of
`RegularityInputsGPK`; all other conjuncts verbatim — `u_prim`, `C₀` before `A` (tex 3999–4000),
(4.6) at the companion pairs (tex 3987–4047; ELLIOT on PRINTs), and for every `A` (tex 4910, 4454)
the outer model family over `𝒪` with sizes at most the cap of (5.1) (tex 4453–4460, 4936–4938,
4954–4956), every model a two-term model of genuine Galois Selmer data (GLUE), the coordinate clause
(tex 3877–3892) and batch 3's outer switching data for every sequence of instances (tex 4940–4950;
GLUE). Kind: definition. -/
def Eq35InputsGenuineABoundedH : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsHPK (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, G.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : CompanionPair W A, vO (G.model i []).coordOf = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst

/-- **(3.5) for each fixed `A` from the homology-level leaf** (tex 2441–2446, 5200–5202): RC16's
`exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`, with the outer processes of batch 3's
`GenuineOuterSwitchData.toOuterSwitchData` at the starting configuration `[]` of the family for
this `A` (the size bound is not used), and the regularity of `RegularityInputsHPK` (through
`RegularityInputsHPK.toS`); `C_R(E, A) = C + C₀ + 2A`. Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsAH (hin : Eq35InputsGenuineABoundedH W) : Eq35Target W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  intro A
  obtain ⟨Pl, G, -, -, hcoord, hsw⟩ := hout A
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => ⟨0, ((hsw inst).toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO
      0).toProcess vO _, [], Eventually.of_forall fun j => hcoord (inst j)⟩)
    (fun i => (hreg i.h i.k i.prepared i.simpleZero i.rough).toS.rc16)
  refine ⟨(C : ℤ) + (C₀ + 2 * (A : ℤ)), ?_⟩
  intro h k' hprep hrank hrough hω
  obtain ⟨uh, huh, -, h35⟩ := hC ⟨h, k', hprep, hrank, hrough, hω⟩
  obtain ⟨t, err, ht, herr, hv⟩ := h46 h k' hprep hrank hrough uh huh
  obtain ⟨hne, hval⟩ := v2_eq_coe_iff.mp hv
  have hcard : k'.natAbs.primeFactors.card ≤ A := by
    have := card_primeFactors_natAbs k'
    omega
  have h46' : |Padic.valuation (centralSpecialization uh) -
      (2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
        ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ))| ≤ C₀ := by
    rw [hval]
    convert herr using 2
    ring
  have key := h35 (W.jrc h k') (omega h : ℤ) (sFun ℓ h) (sFun ℓ (h * k')) C₀
    k'.natAbs.primeFactors (fun p => (t p : ℤ)) hne
    (fun p _ => ⟨Int.natCast_nonneg _, by exact_mod_cast ht p⟩) hcard h46'
  linarith

/-- **(5.5) from the homology-level leaf, through batch 3's `uniform_lower_bound_of_genuine`** (tex
4927–4972): for each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion pair with `ω(k') ≤ A`.
Kind: PROVED from the inputs. -/
theorem eq55_of_inputsAH (hin : Eq35InputsGenuineABoundedH W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ, ∀ i : CompanionPair W A,
      (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, hout⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨Pl, G, -, -, hcoord, hsw⟩ := hout A
  obtain ⟨C, hC⟩ := SwitchInputs.uniform_lower_bound_of_genuine G
    injective_algebraMap_OO isPiAdicOn_two_vO (fun inst => ⟨fun l hl => (hsw inst).step l hl⟩)
  exact ⟨C, fun i => (hC i).trans_eq (hcoord i)⟩

/-- **The old leaf gives the new** (`regularity_GPK_to_HPK` at every companion pair): every witness
of `Eq35InputsGenuineABounded W` is a witness of `Eq35InputsGenuineABoundedH W` with the same data.
Kind: PROVED. -/
theorem Eq35InputsGenuineABounded.toH (hin : Eq35InputsGenuineABounded W) :
    Eq35InputsGenuineABoundedH W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, fun h k' hp hr hro => regularity_GPK_to_HPK (hreg h k' hp hr hro), h46, hout⟩

/-- **Round 9's leaf with sizes equal to the cap gives the new leaf** (through
`eq35InputsGenuineA_iff_bounded`). Kind: PROVED. -/
theorem Eq35InputsGenuineA.toH (hin : Eq35InputsGenuineA W) : Eq35InputsGenuineABoundedH W :=
  Eq35InputsGenuineABounded.toH W ((eq35InputsGenuineA_iff_bounded W).mp hin)

/-- **`Eq35InputsGenuineABoundedH W` is satisfiable** in the degenerate case (no ring instances),
through the old leaf's degenerate witness. Kind: PROVED. -/
theorem eq35InputsGenuineABoundedH_of_not_prepared (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineABoundedH W :=
  Eq35InputsGenuineABounded.toH W (eq35InputsGenuineABounded_of_not_prepared W hW)

end ZInQ.Manuscript.RC.Wiring
