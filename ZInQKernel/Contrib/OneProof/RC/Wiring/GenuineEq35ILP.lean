import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35R
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitAddressPin

/-!
**Theorem 5.3, Lane RC0: the (3.5) leaf with the regularity predicate of the height-one leaf**

Proposition `ex:limits-uniform-lower-bound` (tex 4909–5202) at the ring instances `(h, k')` of
Proposition `ex:sec7-genus-lower` (tex 2418–2446). The leaves ask for the height-one regularity
(tex 4976–5200) twice: at the addresses of the final families, `PrimRegularityInputsILP D` asks
for `RegularityInputsILP ℓ (F.h x) D.kfin u`; at the ring instances, the regularity conjunct of
`Eq35InputsGenuineABoundedR W` asks for `RegularityInputsHPK (uprim h k')`. These are different
predicates: only the first carries the faithful pin, and the second asks for
`HomologySwitchDataPK` at every prime, the first only at quadratic specializations. Both weaken to
the model-level `RegularityInputsMdl` (`RegularityInputsILP.toMdl`, `RegularityInputsHPK.toMdl`).
This file restates the second with the predicate of the first.

* `Eq35InputsGenuineABoundedRP W`: `Eq35InputsGenuineABoundedR W` with the regularity conjunct
  `RegularityInputsILP ℓ h k' (uprim h k')`, under the same quantifiers, all other conjuncts
  verbatim. At a ring instance the predicate is read with the instance's own data, as in the text
  (tex 2413–2414, 2720–2760, 3987–3991): the field `K` quadratic with `√k' ∈ K` (so
  `K = ℚ(√k')`, as `k' < 0`), the curve `E_ℓ ⊗ K` and the characters `χ_h Ψ_i`.
* What the consumers use. `eq35Target_of_inputsAR` passes the conjunct unchanged to
  `eq35Target_of_inputsAH`, which reads it only through `RegularityInputsHPK.toS`, that is through
  `u ∈ Λ[1/2]` (`RegularityInputsHPK.mem_lambdaHalf`, then `regularityInputsS_iff`), as the
  regularity hypothesis of RC16's `exLimitsUniformLowerBound`; that theorem uses the hypothesis
  only through `mem_lambdaHalf_of_regularity`. `eq55_of_inputsAR` does not use the conjunct.
  By `eq35RegularHyp_iff_mem_lambdaHalf` the hypothesis is equivalent to `u ∈ Λ[1/2]`.
* `Eq35InputsGenuineABoundedRL W`: the minimal form, with the conjunct `uprim h k' ∈ Λ[1/2]`.

PROVED: `eq35RegularHyp_iff_mem_lambdaHalf`; `Eq35InputsGenuineABoundedR.toRL` and
`Eq35InputsGenuineABoundedRP.toRL` (both through `RegularityInputsMdl`); `eq35Target_of_inputsARL`
(the proof of `eq35Target_of_inputsAH` re-run on the weaker conjunct, the outer conjunct read
through `eq35R_outerPart_iff`); `eq35Target_of_inputsARP`; `eq55_of_inputsARP`; the degenerate
satisfiability `eq35InputsGenuineABoundedRP_of_not_prepared`.

**Scope.** As for `Eq35InputsGenuineABoundedR`: `uprim` is an existential witness, the outer data
and the configuration families are existential, and their identification with the actual
arithmetic instance is OPEN (ELLIOT + GLUE). Under the pin the coordinate `uprim h k'` is the
coordinate of an integral model of the finite fibre of the retained limit of a moving stage family
of the instance; that family is itself data (GLUE). Unlike an address, a ring instance carries no
separate data coordinate to compare with (no analogue of `IsTExpansion u (D.uPrim F x)`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)
open ZInQ.Contrib.RC53Assist.OuterRealization (RetainedOuterModels RetainedOuterSwitchData
  IsGenuineTwoTermModel eq55_of_retained)

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with the regularity predicate of the height-one leaf** (Proposition
`ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of Proposition
`ex:sec7-genus-lower`, tex 2418–2446): `Eq35InputsGenuineABoundedR W` with its regularity conjunct
`RegularityInputsHPK (uprim h k')` replaced by `RegularityInputsILP ℓ h k' (uprim h k')`, the
faithful pin at every height-one prime `𝔭 ≠ (2)` (tex 4976–5200), read with the instance's own
data: the field `K` quadratic with `√k' ∈ K`, the curve `E_ℓ ⊗ K` and a moving stage family with
characters `χ_h Ψ_i` (tex 2413–2414, 2720–2760, 3987–3991). The quantifiers are those of
`Eq35InputsGenuineABoundedR`, and all other conjuncts are verbatim: `u_prim`, `C₀` before `A`,
(4.6) at the companion pairs (tex 3987–4047), and for every `A` the retained outer family with
sizes at most the cap of (5.1), genuine two-term models, the coordinate clause and the switch
input (tex 4927–4953, 4453–4460). Kind: definition. -/
def Eq35InputsGenuineABoundedRP : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsILP ℓ h k' (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst

/-- **The minimal form of the inputs of (3.5)** (tex 4909–5202, at the ring instances of tex
2418–2446): `Eq35InputsGenuineABoundedR W` with its regularity conjunct replaced by
`uprim h k' ∈ Λ[1/2]` (tex 5190–5194), the only part of the regularity that the consumers read
(`eq35RegularHyp_iff_mem_lambdaHalf`); same quantifiers, all other conjuncts verbatim.
Kind: definition. -/
def Eq35InputsGenuineABoundedRL : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      uprim h k' ∈ lambdaHalfToFrac.range) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst

/-- **The regularity hypothesis of RC16's `exLimitsUniformLowerBound` is `u ∈ Λ[1/2]`** (tex
4976–5200, 5190–5194): the hypothesis gives `u ∈ Λ[1/2]` (`mem_lambdaHalf_of_regularity`, the only
use that theorem makes of it), and `u ∈ Λ[1/2]` gives the hypothesis (one-stage data through
`regularityInputsS_iff`, then `RegularityInputsS.rc16`). Kind: PROVED. -/
theorem eq35RegularHyp_iff_mem_lambdaHalf (u : FractionRing Lambda) :
    (u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u) ↔
      u ∈ lambdaHalfToFrac.range :=
  ⟨mem_lambdaHalf_of_regularity u, fun hu => ((regularityInputsS_iff u).mpr hu).rc16⟩

/-- **The retained form gives the minimal form** (tex 4909–5202, 4976–5200): the regularity
conjunct weakens to `RegularityInputsMdl` (`RegularityInputsHPK.toMdl`) and then to `Λ[1/2]`
(`RegularityInputsMdl.mem_lambdaHalf`); the other conjuncts are unchanged. Kind: PROVED. -/
theorem Eq35InputsGenuineABoundedR.toRL (hin : Eq35InputsGenuineABoundedR W) :
    Eq35InputsGenuineABoundedRL W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, fun h k' hp hr hro => (hreg h k' hp hr hro).toMdl.mem_lambdaHalf, h46, hout⟩

/-- **The pinned form gives the minimal form** (tex 4909–5202, 4976–5200): the regularity conjunct
weakens to `RegularityInputsMdl` (`RegularityInputsILP.toMdl`) and then to `Λ[1/2]`
(`RegularityInputsMdl.mem_lambdaHalf`); the other conjuncts are unchanged. Kind: PROVED. -/
theorem Eq35InputsGenuineABoundedRP.toRL (hin : Eq35InputsGenuineABoundedRP W) :
    Eq35InputsGenuineABoundedRL W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, fun h k' hp hr hro => (hreg h k' hp hr hro).toMdl.mem_lambdaHalf, h46, hout⟩

/-- **(3.5) for each fixed `A` from the minimal form** (tex 2441–2446, 5200–5202): the proof of
`eq35Target_of_inputsAH` on the weaker conjunct. The outer conjunct at `A` is read as the outer
conjunct on old families (`eq35R_outerPart_iff`), whose switching data give the outer processes
at the starting configuration `[]`; the regularity hypothesis of RC16's
`exLimitsUniformLowerBound` comes from `u ∈ Λ[1/2]` (`eq35RegularHyp_iff_mem_lambdaHalf`);
`C_R(E, A) = C + C₀ + 2A`. Kind: PROVED. -/
theorem eq35Target_of_inputsARL (hin : Eq35InputsGenuineABoundedRL W) : Eq35Target W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  intro A
  obtain ⟨Pl, G, -, -, hcoord, hsw⟩ := (eq35R_outerPart_iff W A uprim).mp (hout A)
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => ⟨0, ((hsw inst).toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO
      0).toProcess vO _, [], Eventually.of_forall fun j => hcoord (inst j)⟩)
    (fun i => (eq35RegularHyp_iff_mem_lambdaHalf _).mpr
      (hreg i.h i.k i.prepared i.simpleZero i.rough))
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

/-- **(3.5) for each fixed `A` from the pinned form** (tex 2441–2446, 5200–5202), through the
minimal form (`Eq35InputsGenuineABoundedRP.toRL`, `eq35Target_of_inputsARL`). Kind: PROVED. -/
theorem eq35Target_of_inputsARP (hin : Eq35InputsGenuineABoundedRP W) : Eq35Target W :=
  eq35Target_of_inputsARL W (Eq35InputsGenuineABoundedRP.toRL W hin)

/-- **(5.5) for the coordinates `u_prim`, directly from the pinned form** (tex 4927–4972): for
each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion pair with `ω(k') ≤ A`, from the
retained model family and the switch input on these model data (the RC53 group's
`eq55_of_retained`), as `eq55_of_inputsAR`; the regularity conjunct is not used.
Kind: PROVED. -/
theorem eq55_of_inputsARP (hin : Eq35InputsGenuineABoundedRP W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ, ∀ i : CompanionPair W A,
      (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, hout⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨Pl, T, -, -, hcoord, hsw⟩ := hout A
  exact eq55_of_retained uprim T hcoord hsw

/-- **`Eq35InputsGenuineABoundedRP W` is satisfiable** in the degenerate case (no ring instances;
tex 2418–2446): the regularity conjunct is vacuous, and the other conjuncts are those of the
degenerate witness `eq35InputsGenuineABoundedR_of_not_prepared`. Kind: PROVED. -/
theorem eq35InputsGenuineABoundedRP_of_not_prepared (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineABoundedRP W := by
  obtain ⟨uprim, C₀, -, h46, hout⟩ := eq35InputsGenuineABoundedR_of_not_prepared W hW
  exact ⟨uprim, C₀, fun h _ hp => absurd hp (hW h), h46, hout⟩

end ZInQ.Manuscript.RC.Wiring
