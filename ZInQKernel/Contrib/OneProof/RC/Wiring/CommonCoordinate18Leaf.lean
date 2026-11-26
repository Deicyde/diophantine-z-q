import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18Pin
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST

/-!
# The common-coordinate leaf with the step identities derived from a class provider

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194) through the
inner limit of Lemma `ex:limits-inner-limit` (tex 4385–4451), with the moving character of the
family (tex 2729–2737) and the old Kummer places (tex 2748–2760).

**`CommonCoordinateInputsGenuineK D`** refines the round-13 leaf `CommonCoordinateInputsGenuine D`
(PROVED: `commonCoordinateInputsGenuine_of_K`). Its fields, with their kinds:

* `elliptic` (definition): `E_ℓ` is elliptic;
* `milne` (PRINT, paraphrased; Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with
  the cochain model is GLUE): `MilneADT_I_2_8`;
* `iwasawa` (GLUE: Iwasawa 1955, the tame quotient, joined with the splitting over the wild
  inertia): `IwasawaGenerators`;
* `genuineInj` (`GenuineCochainsInjective`, a statement PROVED by Nöbeling, Invent. Math. 6
  (1968), Thm 2, with Bass–Papp: `genuineCochainsInjective_proved`; the analogous staged leaf
  `CommonCoordinateInputsGenuineS` (`CommonCoordinate19Leaf.lean`) uses it);
* `chains`: a coefficient datum `C`; for every final family ONE nonprincipal ultrafilter on the
  coefficient stages (tex 4401–4404) and ONE moving character `Φ` (`FamilyCharacter`; tex 2737:
  one character for all characters of the family; the intended instance is lane E1's genuine
  `Ψ = (1 + t)^ξ`, `movingPsi_genuine`); and at every address:
  - an actual presentation `A` (`ActualPresentation`, chosen per address: its support `S₀`
    contains the primes of the twist `h_x` and avoids the unused primes, so it cannot be one
    support for the family) whose moving character is the family's on `G_{K,S₀}`
    (`ActualPresentation.FromFamily`, a pin) and whose Kummer places are the places above `2N`
    (`placesAboveTwoN`, a pin; tex 2748–2760), so that `Δ_s` is the text's old condition;
  - the classes `HC` (GLUE, owner lane E2): a class provider at the retained stages, i.e. global
    classes with their global identities `g_{i+1} = e_i g_i + d b_i` at the leaf's point factors
    and their local lifts (`StageClassesAt`). For the text these are lane E2's presentation
    classes of the Kummer classes of the actual anchored Heegner points with their norm identity at
    the switch primes (lane E2's `FullAnchor`, ambient module over `K_{S₁}`). In this structure the
    field is a named hypothesis, met by any provider, the zero provider (`StageClassesAt.zero`)
    included; no surviving declaration pins it (the analogous staged leaf
    `CommonCoordinateInputsGenuineS`, `CommonCoordinate19Leaf.lean`, on `StagedPresentation`, pins
    its own provider to lane E2's classes, `e2ProviderOnS` from `E2ChainInputsS`);
  - the genuine stage chains with these classes (`GenuineStageSTUK`): the step identities are
    DERIVED from the provider, the pins of the classes and functionals, lane RC30's retention and
    the Frobenius data (`exists_stepHyps_provider`); the boundaries and coboundaries are chosen
    witnesses, not fields.

The retractions of the switch quotients onto the two singular blocks are PROVED from `milne`,
`iwasawa`, `genuineInj` (`exists_suppSwitchRetractS_milne`).

**Comparison with the round-13 leaf.** `CommonCoordinateInputsGenuineK →
CommonCoordinateInputsGenuine → CommonCoordinateInputsNF` (PROVED). The new leaf pins the Kummer
places to the places above `2N` and the moving character to the family's, and moves the remaining
content of the step identities into the class provider. In this structure the classes are free, as
in the round-13 leaf, and the step identities are met by a choice of the provider; in the analogous
staged leaf `CommonCoordinateInputsGenuineS` (`CommonCoordinate19Leaf.lean`, on
`StagedPresentation`) the provider is lane E2's Kummer classes of the actual points and the step
identities are derived from lane E2's global identities.

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
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The moving character of the family and the old Kummer places -/

section Family

variable (K : Type) [Field K] [NumberField K]

/-- **The places above `2N`**, `N` the conductor of `E_ℓ` (the newform level; tex 2748–2760):
the text's old Kummer places. The same set as lane RC0's `placesTwoN`. Kind: definition. -/
def placesAboveTwoN (ℓ : ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ((2 * newformLevel (Ecurve ℓ) : ℕ) : 𝓞 K) ∈ v.asIdeal}

/-- **The moving character of a family** (tex 2729–2737): one character `Ψ_s` of `G_{K,S_Ψ}` with
values in `A_s^×` at every stage, for all characters of the family. The intended instance is lane
E1's genuine `Ψ = (1 + t)^ξ` on `G_{K,S_r}` (`movingPsi_genuine`). Kind: definition (data). -/
structure FamilyCharacter : Type where
  /-- the support of the moving character -/
  SΨ : Set (HeightOneSpectrum (𝓞 K))
  /-- the moving character at the stages -/
  Ψ : ∀ s, GKS K SΨ →* (Acoef s)ˣ

/-- The trivial moving character (non-vacuity of `FamilyCharacter`). Kind: definition. -/
def FamilyCharacter.trivial : FamilyCharacter K where
  SΨ := ∅
  Ψ _ := 1

variable {K}

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b}

/-- **The presentation's moving character is the family's** (tex 2729–2737): the support of the
family's character lies in `S₀`, and `ψ_s ∘ π_s` is the family's `Ψ_s` composed with the
restriction `G_{K,S₀} → G_{K,S_Ψ}` at every stage. Kind: definition (a pin). -/
def ActualPresentation.FromFamily (A : ActualPresentation C D Fam x)
    (Φ : FamilyCharacter C.K) : Prop :=
  ∃ h : Φ.SΨ ⊆ A.S₀, ∀ s (g : GKS C.K A.S₀), A.ψ s (A.π s g) = Φ.Ψ s (inflMap C.K h g)

end Family

/-! ### The leaf -/

/-- **The common-coordinate inputs with the step identities derived from a class provider**
(tex 2729–2737, 2748–2760, 4142–4194, 4385–4451): the fields listed in the module docstring, with
their kinds. Kind: definition. -/
structure CommonCoordinateInputsGenuineK {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- `E_ℓ` is elliptic (definition) -/
  elliptic : (Ecurve ℓ).IsElliptic
  /-- PRINT (paraphrased): Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with the
  cochain model is GLUE (tex 3470–3487) -/
  milne : MilneADT_I_2_8
  /-- GLUE: Iwasawa 1955, the tame quotient, joined with the splitting over the wild inertia
  (tex 3470–3480) -/
  iwasawa : IwasawaGenerators
  /-- the genuine local cochain modules are injective at the stage rings (a statement PROVED by
  Nöbeling, Invent. Math. 6 (1968), Thm 2, with Bass–Papp: `genuineCochainsInjective_proved`;
  tex 3470–3480) -/
  genuineInj : GenuineCochainsInjective
  /-- one ultrafilter and one moving character per final family; at every address an actual
  presentation (per address) with the family's moving character and the Kummer places above
  `2N`, a class provider (GLUE, owner lane E2: the presentation classes of the Kummer classes of
  the actual anchored Heegner points with their norm identity at the switch primes; a named
  hypothesis until lane E2's names land), and the genuine stage chains with the provider's
  classes (data, ELLIOT, GLUE; tex 2720–2760, 3455–3498, 4142–4194, 4385–4451) -/
  chains : ∃ C : TateCoef (Ecurve ℓ), ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (Φ : FamilyCharacter C.K),
      ∀ x : Addr F.b, ∃ A : ActualPresentation C D F x,
        A.FromFamily Φ ∧ A.Pk = placesAboveTwoN C.K ℓ ∧
        ∃ (_ : DecidableEq (Places C.K A.S₀)) (G : Set ℕ)
          (HC : ∀ s, s ∈ G → StageClassesAt A s),
          Nonempty (GenuineStageSTUK A milne iwasawa genuineInj U hU G HC)

/-- **The round-13 leaf from the new leaf** (tex 4142–4194, 4385–4451). Kind: PROVED. -/
theorem commonCoordinateInputsGenuine_of_K {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineK D) : CommonCoordinateInputsGenuine D := by
  obtain ⟨hE, h28, hI, hInj, C, hC⟩ := h
  refine ⟨hE, h28, hI, hInj, C, fun Co Ce F hF => ?_⟩
  obtain ⟨U, hU, Φ, hx⟩ := hC Co Ce F hF
  refine ⟨U, hU, fun x => ?_⟩
  obtain ⟨A, -, -, hdec, G, HC, ⟨Gs⟩⟩ := hx x
  exact ⟨A, hdec, Gs.toSTUE, rfl, Gs.pre.hpos⟩

/-- **The current leaf from the new leaf** (tex 4142–4194, 4385–4451): the replacement of
`CommonCoordinateInputsNF` in the leaves. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_genuineK {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineK D) : CommonCoordinateInputsNF D :=
  commonCoordinateInputsNF_of_genuine (commonCoordinateInputsGenuine_of_K h)

/-- **(4.7) from the new leaf** (tex 4142–4194, 4385–4451): `RCSteps.common_coordinate`.
Kind: PROVED. -/
theorem commonCoordinateTarget_of_genuineK {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineK D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_genuineK h)

end ZInQ.Manuscript.RC.Wiring
