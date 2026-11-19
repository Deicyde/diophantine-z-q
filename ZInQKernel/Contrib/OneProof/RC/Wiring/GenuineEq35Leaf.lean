import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineOuter

/-!
**Theorem 5.3, Lane RC0 round 4: the (3.5) leaf on batch 3's genuine switching data**

Proposition `ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of
Proposition `ex:sec7-genus-lower`, tex 2418–2446.

**The defect.** `Eq35InputsGenuineG` (`Wiring/UniformSwitch.lean`) has two switching parts whose
stages are free:

* the height-one part `RegularityInputsS (uprim h k')` at the companion pairs (equivalent to
  `uprim h k' ∈ Λ[1/2]`, `regularityInputsS_iff`);
* the outer part: for every `A` and every sequence of companion pairs, RC0's round-3
  `GenuineOuterSwitchData (hyperfilter ℕ) a` with some starting stage whose coordinates have the
  valuations of `ι_𝒪 (uprim h_j k'_j)`. The stages are chosen per sequence, so a one-stage datum
  (outer dimension one) is available whenever the bound holds (batch 3's truth check, item D2).

**The new leaf** `Eq35InputsGenuineGG W` keeps the data `uprim`, `C₀` and (4.6) verbatim and
re-points both switching parts:

* height-one part: `RegularityInputsG (uprim h k')` (`GenuineSwitchLeaf.lean`: batch 3's
  `GenuineSwitchData` over a configuration family genuine at `𝔭`);
* outer part: ONE family `G` of switched minimal models for all ring instances (batch 3's
  `GenuineOuterModels (2 : 𝒪) (Frac 𝒪) (RingInst W) Pl`: for every ring instance `i` and every
  list `l` of derivative-prime labels the minimal model of the actual Selmer complex of `i` after
  the switches `l`), fixed before any sequence is chosen, with
  - every model a two-term model of genuine Galois Selmer data over `𝒪` (`IsGenuineInstanceModel`:
    a homotopy equivalence from lane RC26's `galoisSelData K S 𝒪 M Δ` to
    `[𝒪^{n+1} --M--> 𝒪^{n+1}]`);
  - the computed coordinate of the actual model `model i []` has the valuation of
    `ι_𝒪 (uprim h k')`;
  - for every `A` and every sequence of companion pairs with `ω(k') ≤ A`, batch 3's
    `GenuineOuterSwitchData (hyperfilter ℕ) G inst`: at every configuration of outer dimension
    `> 1`, a derivative-prime label and the switch GLUE `OuterSwitchStep` between the DETERMINED
    stages `l` and `l ++ [p]`.

PROVED: `eq35Target_of_inputsGG : Eq35InputsGenuineGG W → Eq35Target W` (RC16's
`exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`, with the outer processes of batch 3's
`GenuineOuterSwitchData.toOuterSwitchData` and the regularity of `RegularityInputsG`);
`eq55_of_inputsGG` ((5.5) directly from batch 3's `uniform_lower_bound_of_genuine`);
`eq35InputsGenuineG_regularity_of_GG` (the height-one part implies the round-3 one).

Ties (PROVED): `outer_start_forced` (the starting outer dimension of every sequence is the outer
kernel dimension of the fixed actual models, batch 3's `start_outerDim`, and a datum needing no
switch at the start forces that kernel to be one-dimensional, `outer_collapse_forces`).

**Caveat.** The configuration families and the model family are existential and only required to
be some genuine Galois Selmer data with `t = X`. With one genuine complex of the homotopy type of
`[k --0--> k]` at each `𝔭` (true, not formalized), the regularity part is equivalent to
`uprim h k' ∈ Λ[1/2]` at the companion pairs, Elliot's regularity assertion (ELLIOT). Over the
actual genuine complexes no switch step can be formed (`fG`: `C¹_cont` is infinite-dimensional), so
the actual family witnesses the regularity part only when `s(𝔭) = 1`. UNCLEAR/DEPARTURE of this
leaf: batch 3's `GenuineSwitchData.primitive` requires the actual class to be primitive, which the
text does not supply; `Leaves.lean` uses instead `Eq35InputsGenuineGGPK` (`GenuineSwitchPK.lean`,
the actual classes only nonzero), which this leaf implies (`Eq35InputsGenuineGG.toPK`).
DEPARTURE: one model family with one size function `nOf` is fixed for all ring instances
before `A`, stronger than the text's per-`A` bound (tex 4936–4940, 4453–4463).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx threeTermComplex)
open ZInQ.Manuscript.RC.Determinant (OO)

attribute [local instance] Nat.fact_prime_two

/-! **Genuine instance models over `𝒪`** -/

/-- The integral two-term complex `[R^{n+1} --M--> R^{n+1}]` in degrees one and two (degree zero is
`0`) of a square matrix over a commutative ring. Kind: definition. -/
def integralTwoTerm {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    CochainComplex (ModuleCat.{0} R) ℤ :=
  threeTermComplex (0 : PUnit.{1} →ₗ[R] (Fin (n + 1) → R)) M.mulVecLin (LinearMap.comp_zero _)

/-- **An instance model is a two-term model of genuine Galois Selmer data over `𝒪`** (tex
4927–4940: "write their minimal completed models as `[𝒪_j^n --D_j--> 𝒪_j^n]`", with `𝒪_j = 𝒪`):
there are genuine Galois Selmer data `D` over `𝒪` (`IsGaloisSelData`: lane RC26's
`galoisSelData K S 𝒪 M Δ`, finite support, subcomplex conditions) and a homotopy equivalence from
their Selmer complex to `[𝒪^{n+1} --M--> 𝒪^{n+1}]`. That `D` is the completed actual Selmer complex
of the instance after the given switches is the GLUE identification (owners RC26, RC6, batch 3
RankCounts / HeegnerCohomology). Kind: definition. -/
def IsGenuineInstanceModel {n : ℕ}
    (X : SwitchInputs.InstanceModel (2 : OO) (FractionRing OO) n) : Prop :=
  ∃ D : SelData OO, IsGaloisSelData D ∧
    Nonempty (HomotopyEquiv (selCx D).toCC (integralTwoTerm X.M))

/-! **Ring instances** -/

section Eq35GG

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The ring instances of (3.5)** (tex 2403–2446): pairs `(h, k')` with `h` a known simple zero of
the prepared filter and `k'` a rough companion of `h` (no bound on `ω(k')`). Kind: definition. -/
def RingInst : Type :=
  {p : ℤ × ℤ // W.prepared p.1 ∧ AnalyticRank (Etw ℓ p.1) 1 ∧ W.IsRoughCompanion p.1 p.2}

variable {W}

/-- The ring instance of a companion pair. Kind: definition. -/
def CompanionPair.toInst {A : ℕ} (i : CompanionPair W A) : RingInst W :=
  ⟨(i.h, i.k), i.prepared, i.simpleZero, i.rough⟩

variable (W)

/-- **The inputs of (3.5) on batch 3's genuine switching data** (replaces `Eq35InputsGenuineG W`;
Proposition `ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring instances `(h, k')` of
Proposition `ex:sec7-genus-lower`, tex 2418–2446, with `K = Frac 𝒪`, `v = v_𝒪`, `ι = ι_𝒪` of lane
RC20). Conjuncts (tex; kind; owner):

1. Data `uprim h k' ∈ Frac Λ` (tex 3877–3892, 4911–4913; definition; owner RC15) and `C₀` (the error
   of (4.6), tex 3999–4000; definition; owner RC15).
2. Regularity: `RegularityInputsG (uprim h k')` at every companion pair (tex 4976–5194; batch 3's
   `GenuineSwitchData` over configuration families genuine at `𝔭`; fields and owners at
   `RegularityInputsG`).
3. (4.6) at every companion pair, verbatim from `Eq35InputsGenuineG` (tex 3987–4047; ELLIOT on
   PRINTs Kolyvagin Thm 1, Milne ADT I.7.3, Edixhoven Thm 5.3; owners RC15, RC9).
4. Outer data, fixed by the instances (tex 4927–4972):
   * a label type `Pl` of derivative primes and ONE family `G` of switched minimal models over `𝒪`
     for all ring instances (batch 3's `GenuineOuterModels`; `model i []` the actual minimal model
     of `i`; integral, primitive actual class, integral closed functional with `a = 0`
     (`ex:arith-paired-functional`), admissible complement; tex 4935–4940, 4957–4961, 3864–3869;
     ELLIOT + GLUE; owners RC6, batch 3 RankCounts / HeegnerCohomology / PairedFunctional). The
     common size `nOf l` of the models of one configuration is batch 3's DEPARTURE of form ("fixing
     the bounded `n` on an outer-large set", tex 4936–4938, from (5.1)); DEPARTURE: this one size
     function is global over all ring instances and fixed before `A`, stronger than the text's
     per-`A` bound (tex 4936–4940, 4453–4463);
   * every model is a two-term model of genuine Galois Selmer data over `𝒪`
     (`IsGenuineInstanceModel`; GLUE identification; owners RC26, RC6, batch 3);
   * the computed coordinate of `model i []` has the valuation of `ι_𝒪 (uprim h k')` (tex
     3877–3892: the class-functional coordinate in the retained integral determinant basis; GLUE;
     owners RC15, batch 3);
   * for every `A` and every sequence of companion pairs with `ω(k') ≤ A`, batch 3's
     `GenuineOuterSwitchData (hyperfilter ℕ) G inst` (Elliot's switch lemma for the determined
     configurations: dimension drop and unit coordinate relation, tex 4940–4950; GLUE; owners RC16
     `Switch`, batch 3 SwitchInputs).

PROVED from it (not inputs): `ValuationOfO` (lane RC20), `minor_link`, `cycle_integral`,
`functional_bound` and the nonzero outer class (batch 3's `ofIntegralModels`, `outerClass_ne_zero`),
`pos`, `terminal` (Cramer data, RC16), the outer drop and the equal inner valuations, (5.5),
`u_prim ∈ Λ[1/2]` and (5.5) + (4.6) ⇒ (3.5) (`exLimitsUniformLowerBound`). Kind: definition. -/
def Eq35InputsGenuineGG : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsG (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∃ (Pl : Type) (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (RingInst W) Pl),
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : RingInst W, vO (G.model i []).coordOf = vO (iotaO (uprim i.1.1 i.1.2))) ∧
      ∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G (fun j => (inst j).toInst)

/-- The injectivity of `𝒪 → Frac 𝒪`. -/
theorem injective_algebraMap_OO : Function.Injective (algebraMap OO (FractionRing OO)) :=
  IsFractionRing.injective OO (FractionRing OO)

/-- **(3.5) for each fixed `A` at the rough companions** (tex 2441–2446, 5200–5202) from the new
leaf: RC16's `exLimitsUniformLowerBound` over lane RC20's genuine `𝒪` (`valuationOfO_genuine`), with
the outer processes of batch 3's `GenuineOuterSwitchData.toOuterSwitchData` at the starting
configuration `[]` (whose coordinate is the computed coordinate of the actual model, batch 3's
`coord_start`) and the regularity of `RegularityInputsG`; `C_R(E, A) = C + C₀ + 2A`.
Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsGG (hin : Eq35InputsGenuineGG W) : Eq35Target W := by
  obtain ⟨uprim, C₀, hreg, h46, Pl, G, -, hcoord, hsw⟩ := hin
  intro A
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => ⟨0, ((hsw A inst).toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO
      0).toProcess vO _, [], Eventually.of_forall fun j => hcoord (inst j).toInst⟩)
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

/-- The genuine models restricted to the companion pairs with `ω(k') ≤ A`. Kind: definition. -/
def restrictModels {Pl : Type}
    (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (RingInst W) Pl) (A : ℕ) :
    SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl where
  nOf := G.nOf
  model i l := G.model i.toInst l

/-- **(5.5) from the new leaf, through batch 3's `uniform_lower_bound_of_genuine`** (tex 4927–4972):
for each `A`, `v_𝒪 (ι_𝒪 u_prim) ≥ −C(E, A)` at every companion pair with `ω(k') ≤ A`.
Kind: PROVED from the inputs. -/
theorem eq55_of_inputsGG (hin : Eq35InputsGenuineGG W) :
    ∃ uprim : ℤ → ℤ → FractionRing Lambda, ∀ A : ℕ, ∃ C : ℕ, ∀ i : CompanionPair W A,
      (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨uprim, -, -, -, Pl, G, -, hcoord, hsw⟩ := hin
  refine ⟨uprim, fun A => ?_⟩
  obtain ⟨C, hC⟩ := SwitchInputs.uniform_lower_bound_of_genuine (restrictModels W G A)
    injective_algebraMap_OO isPiAdicOn_two_vO (fun inst => ⟨fun l hl => (hsw A inst).step l hl⟩)
  exact ⟨C, fun i => (hC i).trans_eq (hcoord i.toInst)⟩

/-- The height-one part of the new leaf implies that of the round-3 leaf `Eq35InputsGenuineG`
(`RegularityInputsG.toS`). Kind: PROVED. -/
theorem eq35InputsGenuineG_regularity_of_GG {uprim : ℤ → ℤ → FractionRing Lambda}
    (h : ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsG (uprim h k')) :
    ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsS (uprim h k') :=
  fun a b h1 h2 h3 => (h a b h1 h2 h3).toS

/-! **Ties of the outer part** -/

/-- **The starting stage is fixed by the actual models** (batch 3's `coord_start`,
`start_outerDim`, `outer_collapse_forces`): for every witness of the outer part and every sequence
of companion pairs, the starting stage of the outer switching data is the stage determined by the
fixed models `model i []` of the instances (its outer dimension is that of
`(G.stage 𝒰 inst []).base.toOuterStage`, i.e. by batch 3's `start_outerDim` the kernel dimension of
the genuine outer matrix of those models, so that a datum needing no switch at the start forces that
kernel to be one-dimensional), and its coordinate at `j` is the computed coordinate of the actual
model of `inst j`. Kind: PROVED. -/
theorem outer_start_forced {Pl : Type}
    (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (RingInst W) Pl) (A : ℕ)
    (inst : ℕ → CompanionPair W A)
    (H : SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G (fun j => (inst j).toInst)) :
    ((H.toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO 0).stage []).outerDim =
        (G.stage (Filter.hyperfilter ℕ) (fun j => (inst j).toInst) []).base.toOuterStage.outerDim ∧
      (∀ j, ((H.toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO 0).stage []).coord j =
        (G.model (inst j).toInst []).coordOf) :=
  ⟨rfl, H.coord_start injective_algebraMap_OO isPiAdicOn_two_vO 0⟩

end Eq35GG

end ZInQ.Manuscript.RC.Wiring
