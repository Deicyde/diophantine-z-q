import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Actual
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Pinned

/-!
# The common-coordinate leaf on the genuine complexes of the text's objects

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) through the
inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451).

**`CommonCoordinateInputsGenuine D`** is the replacement offered for the current leaf
`CommonCoordinateInputsNF D`. Its fields, with their kinds:

* `elliptic` (definition): `E_ℓ` is elliptic;
* `milne` (PRINT; Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with the cochain
  model is GLUE, tex 3470–3487): `MilneADT_I_2_8`;
* `iwasawa` (PRINT; Iwasawa, Trans. AMS 80 (1955), p. 448 and §3; tex 3470–3480):
  `IwasawaGenerators`;
* `genuineInj` (GLUE, derivable: Nöbeling, Invent. Math. 6 (1968), Thm 2, with Bass–Papp over a
  Noetherian self-injective ring; tex 3470–3480): `GenuineCochainsInjective`;
* `chains`: a coefficient datum `C`; for every final family ONE nonprincipal ultrafilter on the
  coefficient stages (tex 4401–4404); and at every address `x`:
  - an actual presentation `A : ActualPresentation C D F x` (`CommonCoordinate17Actual.lean`):
    `K = C.K = ℚ(√k)`, the coefficient support `S₀` with `E[2^∞]` rational over `K_{S₀}` (GLUE),
    the conjugation, the twist by `h_x`, the moving character with its prescribed value at the
    first place of each step and its anticyclotomy (GLUE), the Kummer places, the chain's places
    outside `S₀` in split pairs above the unused primes; the objects are then definitions:
    `S = S₀ ∪ {places}`, `M_s = (T₂E ⊗ A_s)(χ_{h_x} Ψ_s)` (lane E2's `MinS` over the stage ring),
    the conditions `Δ_s` (lane RC29's Kummer conditions at the Kummer places, full at the other
    places of `S₀`), the unramified representations `urRep` with `f = urId` and the splits of the
    genuine inflations;
  - genuine stage chains on these objects at the family's ultrafilter (`GenuineStageSTUE`,
    `CommonCoordinate17Pinned.lean`), relaxing the primes in the presentation's order
    (`Gs.ps = A.ps`), retained at nonzero stages only (where `Δ_s` is lane RC29's; at the zero
    ring `StageRing 0` the conditions are the full ones), with the classes pinned to the
    presentation's classes of global classes and
    the relaxed functionals to lane RC30's paired functionals, the step identities (the norm
    identity with its retained boundary as the explicit step input, and the functional relation),
    the leaf's Frobenius data (PROVED on chains built by `actualSteps`,
    `actualSteps_stageFrobAt`), the models of `C_∅` (ELLIOT), and the end identifications
    `hprim`, `htildeE` (`ũ_x = ε_x η_x v_n` with `ε_x ∈ Λ^×`, `ε_x = 1` when `U_x = ∅`).

The retractions of the switch quotients onto the two singular blocks are not inputs: they are
PROVED from `milne`, `iwasawa`, `genuineInj` (`exists_suppSwitchRetractS_milne`, through the
dévissage of the tame comparison, `quasiIso_inflation_ring_of_milne`).

* **`commonCoordinateInputsLimitE_of_genuine`**, **`commonCoordinateInputsNF_of_genuine`**,
  **`commonCoordinateTarget_of_genuine`**: the inner-limit form with the text's unit, the current
  leaf, and (4.7) with `ũ_x = ε_x u_{prim,x}`.
* `genuineStageSTUM_steps_of_noUnused`: at an address without unused primes the step inputs are
  vacuous (non-vacuity of the step part).

**Comparison with the current leaf `CommonCoordinateInputsNF`.**

1. `CommonCoordinateInputsGenuine D → CommonCoordinateInputsNF D` (PROVED,
   `commonCoordinateInputsNF_of_genuine`).
2. The unit is the text's: the end identification is `ũ_x = ε_x η_x v_n` with `ε_x ∈ Λ^×` and
   `ε_x = 1` when `U_x = ∅`, as in the NF form; the pinned form `ε_x = ∏_{q ∈ U_x} q⁻⁴` (cone sign
   `1`, `chainSign_eq_one`; each step `ε = q⁻⁴`) is no longer required.
3. The objects are the text's: `K = ℚ(√k)`, `S = S₀ ∪ {places}` with the places outside `S₀`,
   `M_s = (T₂E ⊗ A_s)(χ_{h_x} Ψ_s)`, `Δ_s` lane RC29's Kummer conditions, the unramified
   representations and the inflations; the step complexes are the genuine Selmer complexes of
   these objects; the NF form has existential triangular models over `Frac Λ` instead, and an
   existential support triangle at a step is equivalent to (4.7) at that step
   (`supportTriangleAt_iff_h47`).
4. No field mentions (4.7), a `KmStep` or the coordinate of an intermediate support; (4.7) at each
   step is a theorem of the matrix identities (`ChainMat.chain_h47`) PROVED from the genuine
   complexes (`toChainMat_holds`).
5. Still conclusion-shaped in part: the global classes are free data (their identification with
   the Kummer classes of the actual points awaits lane E2's repaired ambient module at the switch
   primes), so the step identities can be met by a choice of the global classes, and the
   cup-product data of the retention are not pinned; the identification of the limit of the
   genuine stage models with the genuine Λ-adic complexes (only the matrix identities pass to the
   limit, not the retained homotopy inverses, tex 4403–4404, 4448–4450) is the content of `hprim`
   and `htildeE`. The NF form is equivalent to (4.7) with `ε_x = 1` where no graph prime is unused
   and `u_{prim,x} ∈ F` (for `ℓ > 0` and a support containing `S₀`); this form is not shown to be
   equivalent to anything of the kind.

What stays existential: the coefficient datum `C`; the data fields of the presentation and its
GLUE inputs; the order of the primes; the models of `C_∅` and their ranks; the global classes; the
cup-product data of the retention; the splittings of the inflations; the boundaries and
coboundaries of the step identities; the ultrafilter of each family.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The pinned genuine stage chains on the actual presentation at a fixed ultrafilter**
(tex 3455–3498, 4142–4194, 4385–4451): `GenuineStageSTUE` at `K = C.K`, `S₀`, `S`,
`M = actualM`, `Δ = actualConds`, the places, `X = actualX`, `EU = actualEU`.
Kind: definition. -/
abbrev ActualGenuineStageSTUE {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)}
    {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b} (A : ActualPresentation C D Fam x)
    [DecidableEq (Places C.K A.S₀)] (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    Type 1 :=
  GenuineStageSTUE C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A)
    h28 hI hInj C D Fam x A.pidx U hU

/-- **The common-coordinate inputs on the genuine complexes of the text's objects**
(tex 4142–4194, 4385–4451): the fields listed in the module docstring, with their kinds.
Kind: definition. -/
structure CommonCoordinateInputsGenuine {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- `E_ℓ` is elliptic (definition) -/
  elliptic : (Ecurve ℓ).IsElliptic
  /-- PRINT: Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with the cochain model is
  GLUE (tex 3470–3487) -/
  milne : MilneADT_I_2_8
  /-- PRINT: Iwasawa, Trans. AMS 80 (1955), p. 448 and §3: generators of the tame quotient
  (tex 3470–3480) -/
  iwasawa : IwasawaGenerators
  /-- GLUE, derivable (Nöbeling, Invent. Math. 6 (1968), Thm 2, with Bass–Papp): the genuine
  local cochain modules are injective at the stage rings (tex 3470–3480) -/
  genuineInj : GenuineCochainsInjective
  /-- one ultrafilter per final family, and at every address the actual presentation with the
  pinned genuine stage chains on it, relaxing the primes in the presentation's order, at
  nonzero stages (where the conditions are lane RC29's) (data, ELLIOT, GLUE; tex 2720–2741,
  3455–3498, 4142–4194, 4385–4451) -/
  chains : ∃ C : TateCoef (Ecurve ℓ), ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite), ∀ x : Addr F.b,
      ∃ A : ActualPresentation C D F x, ∃ _ : DecidableEq (Places C.K A.S₀),
        ∃ Gs : ActualGenuineStageSTUE A milne iwasawa genuineInj U hU,
          Gs.ps = A.ps ∧ ∀ s ∈ Gs.G, 0 < s

/-- **The inner-limit inputs with the text's unit from the genuine complexes** (tex 4142–4194,
4385–4451). Kind: PROVED. -/
theorem commonCoordinateInputsLimitE_of_genuine {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuine D) : CommonCoordinateInputsLimitE D := by
  obtain ⟨hE, h28, hI, hInj, C, hC⟩ := h
  refine ⟨hE, C, fun Co Ce F hF => ?_⟩
  obtain ⟨U, hU, hx⟩ := hC Co Ce F hF
  refine ⟨U, hU, fun x => ?_⟩
  obtain ⟨A, _, Gs, -⟩ := hx x
  exact ⟨Gs.toLimitSTE⟩

/-- **The current leaf from the genuine complexes** (tex 4142–4194, 4385–4451): the replacement
of `CommonCoordinateInputsNF` in the leaves. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_genuine {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuine D) : CommonCoordinateInputsNF D :=
  commonCoordinateInputsNF_of_limitE (commonCoordinateInputsLimitE_of_genuine h)

/-- **(4.7) from the genuine complexes** (tex 4142–4194, 4385–4451): `RCSteps.common_coordinate`.
Kind: PROVED. -/
theorem commonCoordinateTarget_of_genuine {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuine D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_genuine h)

/-- **At an address without unused primes the step inputs are vacuous** (tex 4142–4194): for
`ps = []` the chain has no switch, so the step inputs and the Frobenius data of the stage chains
hold for any traces, boundaries and coboundaries. Kind: PROVED. -/
theorem genuineStageSTUM_steps_of_noUnused {ι : Type} [DecidableEq ι]
    {Cx : ∀ s, Finset ι → GCx (StageRing s)}
    {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
    {m0 m1 m2 : ℕ} {pidx : ℕ → ι} (s : ℕ) (cd : CMChainData (Cx s) (Ex s) m0 m1 m2 pidx 0)
    (a : ℕ → StageRing s) (bw : ∀ i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) (f : FrobSeq LamI) :
    CMStepHyps cd a bw μ ∧ StageFrobAt f s cd a :=
  ⟨⟨fun i h => absurd h (Nat.not_lt_zero i), fun i h => absurd h (Nat.not_lt_zero i)⟩,
    fun i h => absurd h (Nat.not_lt_zero i)⟩

end ZInQ.Manuscript.RC.Wiring
