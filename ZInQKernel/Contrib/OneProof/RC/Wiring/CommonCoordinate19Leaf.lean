import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Unit
import ZInQKernel.Contrib.RC53Assist.NoetherianInjective.GenuineInjective

/-!
# The common-coordinate leaf on the presentation with staged supports

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) through the
inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451), with the moving character of
Proposition `ex:arith-moving-character` (tex 2729–2737: `Ψ_i = (1 + t)^{ψ_i}`, ramified at the
moving prime `r_i`, the same for all characters of the family) and the Heegner points of
tex 2914–2936.

**`CommonCoordinateInputsGenuineS D`**: per final family one nonprincipal ultrafilter and ONE
moving character `G`, lane RC0's `GenuineFamilyMovingCharacter` (the genuine ring-class
realization; lane E1's `exists_genuineFamilyMovingCharacter` produces one for the curve, and its
`toFamily` is the `FamilyMovingCharacter` of lane RC0's inner-limit leaf, so one family character
serves both leaves); at every address a presentation `StagedPresentation C D F x G.toFamily`
whose support at the stage `s` is `S₀ s ⊇ Sr(s)` (`CommonCoordinate19Staged.lean`); at every
retained stage `t + 1` the inputs of lane E2's Kummer classes of the actual Heegner points
(`E2ChainInputsS`, `CommonCoordinate19E2.lean`, with `ThetaOfDelta` and the splitting of the
step primes DERIVED); and the genuine stage chains with these classes (`GenuineStageSTUS`,
`CommonCoordinate19Pin.lean`, with the provider PINNED to lane E2's `e2ProviderS`, and the step
identities derived).

* `e2ProviderOnS`: the provider at the retained stages;
* **`commonCoordinateInputsLimitE_of_S`**, **`commonCoordinateInputsNF_of_genuineS`**,
  **`commonCoordinateTarget_of_genuineS`** (PROVED): the inner-limit form with one ultrafilter
  per family (`CommonCoordinateInputsLimitE`), the current leaf `CommonCoordinateInputsNF` and
  (4.7).

The injectivity of the genuine local cochain modules is PROVED (`genuineCochainsInjective_proved`),
so the switch retractions rest on `MilneADT_I_2_8` (PRINT, paraphrased) and `IwasawaGenerators`
(GLUE) only.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Local (IwasawaGenerators genuineCochainsInjective_proved)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b}

/-- **Lane E2's provider at the retained stages** (tex 4157–4172, 4385–4451): at a stage `t + 1`
of the retained set the provider `e2ProviderS` of the inputs at that stage; at the stage `0`
(never retained) the zero provider. Kind: definition. -/
noncomputable def e2ProviderOnS {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}
    (P : StagedPresentation C D Fam x G.toFamily) {Gs : Set ℕ}
    (I : ∀ t, t + 1 ∈ Gs → E2ChainInputsS P t) : ∀ s, s ∈ Gs → StageClassesAtS P s
  | 0, _ => StageClassesAtS.zero P 0
  | t + 1, h => e2ProviderS P t (I t h)

/-- The provider at a positive stage is lane E2's (tex 4157–4172). Kind: PROVED. -/
theorem e2ProviderOnS_succ {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}
    (P : StagedPresentation C D Fam x G.toFamily) {Gs : Set ℕ}
    (I : ∀ t, t + 1 ∈ Gs → E2ChainInputsS P t) (t : ℕ) (h : t + 1 ∈ Gs) :
    e2ProviderOnS P I (t + 1) h = e2ProviderS P t (I t h) :=
  rfl

/-- **The common-coordinate inputs on the presentation with staged supports** (tex 2729–2737,
2914–2936, 4142–4194, 4385–4451). Kind: definition. -/
structure CommonCoordinateInputsGenuineS {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- `E_ℓ` is elliptic (definition) -/
  elliptic : (Ecurve ℓ).IsElliptic
  /-- PRINT (paraphrased): Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with the
  cochain model is GLUE (tex 3470–3487) -/
  milne : MilneADT_I_2_8
  /-- GLUE: Iwasawa 1955, the tame quotient, joined with the splitting over the wild inertia
  (tex 3470–3480) -/
  iwasawa : IwasawaGenerators
  /-- per final family one nonprincipal ultrafilter (tex 4401–4404) and one moving character, the
  genuine ring-class realization (lane RC0's `GenuineFamilyMovingCharacter`; tex 2729–2737,
  3500–3702); at every address a presentation with the support `S₀ s ⊇ Sr(s)` at the stage `s`
  and the family's character, the inputs of lane E2's Kummer classes of the actual Heegner
  points at every retained stage (PRINT, definitions: `E2ChainInputsS`), and the genuine stage
  chains with these classes (data, ELLIOT, GLUE; tex 2720–2760, 3455–3498, 4142–4194,
  4385–4451) -/
  chains : ∃ C : TateCoef (Ecurve ℓ), ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
      (G : GenuineFamilyMovingCharacter C.K ℓ F.Q),
      ∀ x : Addr F.b, ∃ (P : StagedPresentation C D F x G.toFamily)
        (_ : ∀ s, DecidableEq (Places C.K (P.S₀ s))) (Gs : Set ℕ)
        (I : ∀ t, t + 1 ∈ Gs → E2ChainInputsS P t),
        Nonempty (GenuineStageSTUS P milne iwasawa genuineCochainsInjective_proved U hU Gs
          (e2ProviderOnS P I))

/-- **The inner-limit form from the leaf on the staged presentation** (tex 4142–4194, 4385–4451):
at every address the inner-limit data `GenuineStageSTUS.toLimitSTE` at the family's ultrafilter.
Kind: PROVED. -/
theorem commonCoordinateInputsLimitE_of_S {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineS D) : CommonCoordinateInputsLimitE D := by
  obtain ⟨hE, h28, hI, C, hC⟩ := h
  refine ⟨hE, C, fun Co Ce F hF => ?_⟩
  obtain ⟨U, hU, G, hx⟩ := hC Co Ce F hF
  refine ⟨U, hU, fun x => ?_⟩
  obtain ⟨P, hdec, Gs, I, ⟨S⟩⟩ := hx x
  exact ⟨S.toLimitSTE⟩

/-- **The current leaf from the leaf on the staged presentation** (tex 4142–4194, 4385–4451): the
replacement of `CommonCoordinateInputsNF` in the leaves. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_genuineS {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineS D) : CommonCoordinateInputsNF D :=
  commonCoordinateInputsNF_of_limitE (commonCoordinateInputsLimitE_of_S h)

/-- **(4.7) from the leaf on the staged presentation** (tex 4142–4194, 4385–4451):
`RCSteps.common_coordinate`. Kind: PROVED. -/
theorem commonCoordinateTarget_of_genuineS {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineS D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_genuineS h)

end ZInQ.Manuscript.RC.Wiring
