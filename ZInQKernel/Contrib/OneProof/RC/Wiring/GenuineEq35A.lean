import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchPK
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineOuterTies

/-!
# Theorem 5.3, Lane RC0 round 9: the (3.5) leaf in the text's quantifier order

Proposition `ex:limits-uniform-lower-bound` (tex 4909–5202) at the ring instances of Proposition
`ex:sec7-genus-lower` (tex 2418–2446). The text fixes `A` first (tex 2442–2446, 4454, 4663–4666,
4719, 4910) and controls the size of the models only through (5.1),
`N(E, A, j) ≤ 56 ω(2N) + 8A + 56 j + 70` (tex 4453–4460, 4473, 4644–4647, 4954–4956). The previous
leaf `Eq35InputsGenuineGGPK` chose ONE model family for all ring instances before `A`, with one
size function `nOf` bounding the starting ranks of all instances, a bound independent of `A` that
the text never states (the final review's R3-5).

`Eq35InputsGenuineA W` restates the leaf:

1. the data `u_prim`, `C₀`, the regularity of the primitive coordinates (`RegularityInputsGPK`) and
   (4.6) are chosen before `A`, as in the text (tex 3999–4000);
2. for every `A`, a model family indexed by the companion pairs with `ω(k') ≤ A`
   (`CompanionPair W A`), with the coordinate clause at those instances, and the switching data
   for every sequence of them;
3. the size of the models at a configuration of `j` switches is the cap of (5.1),
   `nOf l = eq51Cap ℓ A |l|` (`N` the level of `E_ℓ`): the text's models have size at most the cap,
   and padding a model by contractible blocks `[𝒪 --(-1)--> 𝒪]` keeps its coordinate exactly, its
   outer dimension and the switch steps (`GenuineEq35Pad.lean`; blocks `[𝒪 --1--> 𝒪]` would change
   the coordinate by the sign `(-1)^k`); so the models are the text's models up to that padding,
   not necessarily minimal. The leaf in the text's form, with the sizes at most the cap, is
   `Eq35InputsGenuineABounded`, equivalent to this one (`eq35InputsGenuineA_iff_bounded`). The
   bound is on the matrix index `nOf`; each free term has rank `nOf + 1`. The text's total-rank
   estimate `2 * (nOf + 1) ≤ eq51Cap` implies this weaker bound. The exact-size auxiliary form
   pads the index to the cap and may exceed the text's literal total-rank cap, while retaining a
   bound depending only on `E`, `A` and `j`.

PROVED: `eq35Target_of_inputsA` ((3.5) for each `A`, RC16's `exLimitsUniformLowerBound` over lane
RC20's genuine `𝒪`), `eq55_of_inputsA` ((5.5) through batch 3's `uniform_lower_bound_of_genuine`),
the ties `outer_start_forcedA`, and the degenerate satisfiability
`eq35InputsGenuineA_of_not_prepared` (no ring instances). The model family is existential: the
genuine Galois Selmer data in `IsGenuineInstanceModel` are not tied to the instance `i`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter
open ZInQ.Manuscript.RC.Determinant (OO)

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The cap of (5.1)** (Lemma `ex:limits-residual-bound`, tex 4453–4460):
`N(E, A, j) = 56 ω(2N) + 8A + 56 j + 70`, with `N` the level of `E_ℓ`. Kind: definition. -/
def eq51Cap (ℓ A j : ℕ) : ℕ :=
  56 * (2 * CST.newformLevel (Ecurve ℓ)).primeFactors.card + 8 * A + 56 * j + 70

/-- **The inputs of (3.5), in the text's quantifier order** (Proposition
`ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of Proposition
`ex:sec7-genus-lower`, tex 2418–2446). Conjuncts (tex; kind; owner):
1. data `uprim h k' ∈ Frac Λ` (tex 3877–3892, 4911–4913; definition; owner RC15) and `C₀` (the
   error of (4.6), tex 3999–4000; definition; owner RC15), chosen before `A`;
2. regularity: `RegularityInputsGPK (uprim h k')` at every companion pair (tex 4976–5194; the actual
   classes nonzero, the primitive kernel vectors PROVED; fields and owners at
   `RegularityInputsGPK`);
3. (4.6) at every companion pair (tex 3987–4047; ELLIOT on GLUE Kolyvagin Thm 1
   (cited statement) and PRINTs Milne ADT I.7.3, Edixhoven Thm 5.3; owners RC15, RC9);
4. for every `A` (tex 4910, 4454): a label type `Pl` of derivative primes and a family `G` of
   switched models over `𝒪` for the companion pairs with `ω(k') ≤ A` (batch 3's
   `GenuineOuterModels`; `model i []` the actual model of `i`; integral, primitive actual class,
   integral closed functional with `a = 0`, admissible complement; tex 4935–4940, 4957–4961,
   3864–3869; ELLIOT + GLUE; owners RC6, batch 3), with
   * the size at a configuration of `j` switches the cap of (5.1), `eq51Cap ℓ A j` (tex 4936–4938,
     4954–4956; the text's models have size at most the cap, padded by contractible blocks
     `[𝒪 --(-1)--> 𝒪]`, which keep the coordinate, the outer dimension and the switch steps,
     `GenuineEq35Pad.lean`);
   * every model a two-term model of genuine Galois Selmer data over `𝒪` (`IsGenuineInstanceModel`;
     GLUE identification; owners RC26, RC6, batch 3; the Galois data are existential, not tied to
     the instance);
   * the computed coordinate of `model i []` with the valuation of `ι_𝒪 (uprim h k')` at those
     instances (tex 3877–3892; GLUE; owners RC15, batch 3);
   * for every sequence of those instances, batch 3's `GenuineOuterSwitchData (hyperfilter ℕ) G`
     (Elliot's switch lemma for the determined configurations: dimension drop and unit coordinate
     relation, tex 4940–4950; GLUE; owners RC16 `Switch`, batch 3 SwitchInputs).

Kind: definition. -/
def Eq35InputsGenuineA : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsGPK (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∀ A : ℕ, ∃ (Pl : Type)
      (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, G.nOf l = eq51Cap ℓ A l.length) ∧
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : CompanionPair W A, vO (G.model i []).coordOf = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst

/-- **(3.5) for each fixed `A` at the rough companions** (tex 2441–2446, 5200–5202): RC16's
`exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`, with the outer processes of batch 3's
`GenuineOuterSwitchData.toOuterSwitchData` at the starting configuration `[]` of the family for
this `A`, and the regularity of `RegularityInputsGPK`; `C_R(E, A) = C + C₀ + 2A`. Kind: PROVED
from the inputs. -/
theorem eq35Target_of_inputsA (hin : Eq35InputsGenuineA W) : Eq35Target W := by
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

/-- **(5.5) from the new leaf, through batch 3's `uniform_lower_bound_of_genuine`** (tex
4927–4972): for each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion pair with `ω(k') ≤ A`.
Kind: PROVED from the inputs. -/
theorem eq55_of_inputsA (hin : Eq35InputsGenuineA W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ, ∀ i : CompanionPair W A,
      (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, hout⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨Pl, G, -, -, hcoord, hsw⟩ := hout A
  obtain ⟨C, hC⟩ := SwitchInputs.uniform_lower_bound_of_genuine G
    injective_algebraMap_OO isPiAdicOn_two_vO (fun inst => ⟨fun l hl => (hsw inst).step l hl⟩)
  exact ⟨C, fun i => (hC i).trans_eq (hcoord i)⟩

/-- **The starting stage is fixed by the actual models of the family for `A`** (batch 3's
`coord_start`, `start_outerDim`): for every family of the leaf and every sequence of companion
pairs with `ω(k') ≤ A`, the starting stage of the outer switching data is the stage determined by
the models `model i []`, and its coordinate at `j` is the computed coordinate of the actual model
of `inst j`. Kind: PROVED. -/
theorem outer_start_forcedA {Pl : Type} {A : ℕ}
    (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl)
    (inst : ℕ → CompanionPair W A)
    (H : SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst) :
    ((H.toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO 0).stage []).outerDim =
        (G.stage (Filter.hyperfilter ℕ) inst []).base.toOuterStage.outerDim ∧
      (∀ j, ((H.toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO 0).stage []).coord j =
        (G.model (inst j) []).coordOf) :=
  ⟨rfl, H.coord_start injective_algebraMap_OO isPiAdicOn_two_vO 0⟩

/-- **`Eq35InputsGenuineA W` is satisfiable**: it holds when the prepared filter is empty (no
companion pairs; for each `A` the model family over the empty instance type, of the size of the
cap). Kind: PROVED. -/
theorem eq35InputsGenuineA_of_not_prepared (hW : ∀ h, ¬ W.prepared h) : Eq35InputsGenuineA W :=
  ⟨fun _ _ => 0, 0, fun h _ hp _ _ => (hW h hp).elim, fun h _ hp _ _ _ _ => (hW h hp).elim,
    fun A => ⟨Empty, ⟨fun l => eq51Cap ℓ A l.length, fun i _ => (hW _ i.prepared).elim⟩,
      fun _ => rfl, fun i _ => (hW _ i.prepared).elim, fun i => (hW _ i.prepared).elim,
      fun inst => (hW _ (inst 0).prepared).elim⟩⟩

end ZInQ.Manuscript.RC.Wiring
