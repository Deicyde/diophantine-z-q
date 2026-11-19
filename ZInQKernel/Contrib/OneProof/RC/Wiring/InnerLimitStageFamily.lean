import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitSwitchModel
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Realized
import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.FullTransport
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageProjectionModel

/-!
# Theorem 5.3, Lane RC0 round 15: the inner-limit switch on a fixed-old-support stage family

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5195), with the switch
at a derivative label on the inner-limit objects (tex 4385–4451, 4834–4907, 5027–5086).

**The support convention** (tex 5056–5062): at the new prime `q_i` the stage complex carries no
Selmer condition. The truncated conditions `D⁰` and `D⁰ ⊕ (F ⊕ S)[−1]` are imposed afterwards,
through the localization to the split local model. The stage family of the RC53 group realizes
this directly. Its global complex at stage `i` is the Selmer complex of the enlarged support
`insert q_i S`, with local conditions only at the old places `S`, and `q_i ∉ S`. The inputs below
are stated on that family, with the RC53 group's split-stage records, so no condition at `q_i` has
to be named and the RC53 group's producers apply verbatim.

**DEPARTURE.** The family's old support `S` and its characters `α_i` of `G_{K,S}` are fixed across
the stages. This is a fixed-old-support auxiliary case, not the manuscript's stage family: the
text's characters `χ_h Ψ_i` ramify at conductor primes `r_i` that vary with the stage and need not
be restrictions of one character (tex 2727–2741, 4268–4272), and an injective sequence of such
conductors cannot descend to one finite support.

* `ILStageStepFamily`: the inputs of one switch on the stage family (old support `S`, the support
  of the actual conjugation). PROVED: `ILStageStepFamily.toILStageStep` (the flat terms by
  `ActualStageFamily.flat`; the residue identity of tex 5037 by
  `RetainedLocalArithmetic.hloc_at_conj`, with `σ = 1`, `ε₀ = −ε`, `ε₂ = ε`) and
  `ILStageStepFamily.stepData`.
* `ILStageStepFamilyLinked`: with the links (on a `U`-large set of positive stages the split
  projection a quasi-isomorphism over `A_i` onto the zero-differential split model; on a `U`-large
  set the retained
  realization on the family's stage complexes, in the RC53 group's form
  `RetainedStageRealization`). PROVED: `projection_model_of_homotopyEquiv`.
* `ILStageStepFamilyLinked.ofAssembled`: the RC53 group's realized assembly supplies every field
  but the retained local arithmetic, the detection, the side-to-stage isomorphisms and the
  quasi-isomorphism link of the projection. Kind: PROVED.
* `InnerLimitSwitchFamily`: the frame and linked family switches with side models. PROVED:
  `toInner`, `regular_of_innerLimitSwitchFamily`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  conjMatrix transportedPairing localPairingOfMat splitSelData stageLocMat stagePairingInputOfSel)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide Vec2)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS NekovarProp788ii)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (ActualStageFamily SplitStage
  stageRes RetainedStageRealization ArithmeticInputs AssembledLimit OldDualityData
  StandardOldReference ArithmeticPrints ResidualSupportControl ActualSupportPresentation
  StageArithmeticInput)
open ZInQ.Contrib.RC53Assist.ResidueIdentity (RetainedLocalArithmetic RetainedZeroTwo)

/-! **The inputs of one switch on the stage family** -/

section Step

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The inputs of one switch on the stage family of the text** (tex 4385–4451, 4834–4907,
5027–5086); the old support is `S`, the support of the actual conjugation:
* `hS`, `α`, `hα`: `S` finite and the coefficient characters on `G_{K,S}` (data and ELLIOT); not
  the text's moving characters `χ_h Ψ_i`, which ramify at primes `r_i` varying with the stage (tex
  2727–2741, 4268–4272);
* `Fam`: the RC53 group's stage family, with the new primes `q_i ∉ S` and the old conditions
  (data and GLUE, tex 4401–4406, 4809–4830, 5055–5059); `hOld`: flat terms of the old conditions
  other than zero and full (GLUE);
* `hres`, `B`, `hbdd`, `hB`: finite residual cohomology of the stage complexes, the range
  `[0, 3]` and a uniform bound (ELLIOT, tex 4401–4406; the RC53 group's
  `actualResidualPackage_of_support_change` gives them from the fixed-support bounds by a change of
  support at one new place);
* `Uq`, `ιq`, `stages`: the condition at the derivative label and the split-stage records (the
  split projection, the self-paired split Selmer datum, its trace, the global-duality
  quasi-isomorphism; GLUE, tex 4385–4451, 4859–4873);
* `U`, `hU`, `C`, `D`, `E`, `hlift`, `hrank`, `hrankB`: the ultrafilter and a retained realization
  (data, tex 4385–4451);
* `rla`, `h02`, `hJ`: the retained local arithmetic at the derivative label, its zero/two
  realization and the identification of its conjugation matrix with `ρ_T(τ)` (GLUE, tex
  4860–4863, 5027–5043); the residue identity of tex 5037 is PROVED from them;
* `hdet`: the detection `F ≤ U` (ELLIOT + GLUE: Lemma `ex:limits-kernel-detection`, tex
  4748–4833, applied at tex 4997–5001);
* `φ`, `φ'`: the side-to-stage isomorphisms (GLUE, tex 4986–4991, 5072–5080).
Kind: definition (inputs). -/
structure ILStageStepFamily (Z₀ Z₁ : TwoTermStage ι) where
  /-- The old support is finite. -/
  hS : S.Finite
  /-- The coefficient characters. -/
  α : ∀ i, GKS K S →* (Acoef i)ˣ
  [hα : ∀ i, IsOpenKer (α i)]
  /-- The stage family: the new primes and the old conditions. -/
  Fam : ActualStageFamily S W α
  /-- Flat terms of the old conditions other than zero and full. -/
  hOld : Fam.NontrivialOldFlat
  /-- Finite residual cohomology of the stage complexes. -/
  hres : ∀ i [NeZero i], ResidualCohomologyFinite (Fam.globalCx i)
  /-- The uniform bound. -/
  B : ℕ
  /-- The range `[0, 3]`. -/
  hbdd : ∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (Fam.globalCx i) n) = 0
  /-- The residual ranks are bounded by `B`. -/
  hB : ∀ i [NeZero i] (n : ℤ),
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (Fam.globalCx i) n) ≤ B
  /-- The condition at the derivative label. -/
  Uq : ∀ i, GCx (Acoef i)
  /-- Its map to the local cochains. -/
  ιq : ∀ i, GHom (Uq i) (Fam.localCx i)
  /-- The split-stage records. -/
  stages : ∀ i, SplitStage Fam i (Uq i) (ιq i)
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The retained stage complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- The retained pairing data. -/
  D : RetainedLimitPairingStages U C
  /-- The retained global duality. -/
  E : RetainedGlobalDualityStages D
  /-- The retained local pairing lifts the stage local pairings. -/
  hlift : ∀ i, i ≠ 0 → ∀ a b,
    (D.loc a b i).map (stageMap i) = stageLocMat (stages i).pairing (stages i).trace a b
  /-- The model ranks are the residual ranks of the stage complexes on a `U`-large set. -/
  hrank : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (Fam.globalCx i) n)
  /-- The model ranks are bounded by `B`. -/
  hrankB : ∀ n, C.rank n ≤ B
  /-- The retained local arithmetic at the derivative label. -/
  rla : RetainedLocalArithmetic U C D
  /-- Its zero/two matrix is the transported zero/two cup. -/
  h02 : RetainedZeroTwo rla
  /-- Its conjugation matrix is `ρ_T(τ)` at the fibre. -/
  hJ : rla.JAt P = conjMatrix Cn W hW P
  /-- Detection `F ≤ U`. -/
  hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
    (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U
  /-- The finite side and the stage `Z₀`. -/
  φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
    1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀
  /-- The singular side and the stage `Z₁`. -/
  φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
    (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁

attribute [instance] ILStageStepFamily.hα

variable {P Cn W hW}

/-- **`ILStageStep` from the inputs on the stage family**: the stage complexes are the family's,
their localization is `stageRes` with the split projection, `hflat` is `ActualStageFamily.flat`,
and the residue identity is `RetainedLocalArithmetic.hloc_at_conj` (`ε₀ = −ε`, `ε₂ = ε`,
`σ = 1`). Kind: PROVED. -/
def ILStageStepFamily.toILStageStep {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamily P Cn W hW Z₀ Z₁) : ILStageStep P Cn W hW Z₀ Z₁ where
  U := X.U
  hU := X.hU
  G := X.Fam.globalCx
  hflat := X.Fam.flat X.hS X.hOld
  Uc := X.Uq
  res i := stageRes X.Fam i (X.stages i).projection
  ιc i := ghomComp (X.ιq i) (X.stages i).projection
  Q i := (X.stages i).pairing
  tr i := (X.stages i).trace
  htr i := (X.stages i).trace_kills
  hdual i := (X.stages i).duality
  hres := X.hres
  lo := 0
  hi := 3
  hbdd := X.hbdd
  B := X.B
  hB := X.hB
  C := X.C
  D := X.D
  E := X.E
  hlift := X.hlift
  hrank := X.hrank
  hrankB := X.hrankB
  ε₀ := X.rla.ε₀At P
  ε₂ := X.rla.ε₂At P
  ε := X.rla.εAt P
  σ := 1
  hε₂ := X.rla.ε₂At_ne_zero P
  hε := X.rla.εAt_ne_zero P
  hσ := one_ne_zero
  hloc := X.rla.hloc_at_conj X.h02 X.hU P Cn W hW X.hJ
  hdet := X.hdet
  φ := X.φ
  φ' := X.φ'

/-- The inner-limit step data of the inputs on the stage family. Kind: definition. -/
abbrev ILStageStepFamily.stepData {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamily P Cn W hW Z₀ Z₁) : InnerLimitStepData P Z₀ Z₁ :=
  X.toILStageStep.toStepData

variable (P Cn W hW) in
/-- **The inputs of one switch on the stage family, with their links** (tex 4385–4451,
4859–4868):
* `projection_model`: on a `U`-large set of positive stages the split projection at `q_i` is a
  quasi-isomorphism over `A_i` of the local cochains with the split model
  `D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]`, whose differential is zero (tex 4860–4862; GLUE). Eventuality
  weakens the stage quantifier, not the coefficient ring: the genuine label precision must cover
  `A_i`. The supplied same-stage trivial-action and fixed-root hypotheses and the normalized
  retract prove the stronger homotopy-equivalence property, which implies it
  (`projection_model_of_homotopyEquiv`);
* `realized`: on a `U`-large set of positive stages the retained data are realized on the family's
  stage complexes: a finite free model with a normalized retract and coordinates in which the
  model's differential, its localization and its global trace pairing are the stage images of
  `C.d`, `D.res`, `D.glob` (the RC53 group's `RetainedStageRealization`). These are equalities on
  the chosen models; the RC53 group's realized assembly supplies them
  (`ILStageStepFamilyLinked.ofAssembled`).
At the new prime no condition is named: the relaxed condition of the switch is
`D⁰ ⊕ (F ⊕ S)[−1]`, not the full local complex (tex 4874–4876), and it enters only through the
split model.
Kind: definition (inputs). -/
structure ILStageStepFamilyLinked (Z₀ Z₁ : TwoTermStage ι) extends
    ILStageStepFamily P Cn W hW Z₀ Z₁ where
  /-- On a `U`-large set of stages the split projection is a quasi-isomorphism over `A_i`. -/
  projection_model : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i],
    QuasiIso (GHom.toCC (stages i).projection)
  /-- The retained data are realized on the family's stage complexes. -/
  realized : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], Nonempty
    (RetainedStageRealization C D i
      (stagePairingInputOfSel (stages i).pairing (stages i).trace (stages i).trace_kills))

/-- **An exact homotopy equivalence gives the projection link**: if at every positive stage the
split projection is the forward map of a homotopy equivalence (the RC53 group's normalized local
retraction), it is a quasi-isomorphism on every `U`-large set. Kind: PROVED. -/
theorem projection_model_of_homotopyEquiv {A : ℕ → Type} [∀ i, CommRing (A i)]
    {X Y : ∀ i, GCx (A i)} (pr : ∀ i, GHom (X i) (Y i)) (U : Ultrafilter ℕ)
    (h : ∀ i [NeZero i], ∃ e : HomotopyEquiv (X i).toCC (Y i).toCC, e.hom = GHom.toCC (pr i)) :
    ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], QuasiIso (GHom.toCC (pr i)) :=
  Filter.Eventually.of_forall fun i _ => by
    obtain ⟨e, he⟩ := h i
    rw [← he]
    exact e.quasiIso_hom

end Step

/-! **The RC53 group's realized assembly supplies the inputs** -/

section Assembled

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  {α : ∀ i, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  {Fam : ActualStageFamily S W α} {O : OldDualityData Fam} {R : StandardOldReference S W α}
  {width : ℕ} {a : ArithmeticInputs Fam O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ cofinite}

/-- **The linked inputs from the RC53 group's realized assembly** (`assemble_inner_limit_realized`,
`assemble_from_support_change_realized`): the split-stage records, the retained data, their stage
lifts and ranks, the realization on the family's stage complexes, and the residual package
(`ResidualSupportControl.residual_finite`, `producerBounds`) come from the assembly. The remaining
inputs are the retained local arithmetic (`rla`, `h02`, `hJ`), the detection, the side-to-stage
isomorphisms and the quasi-isomorphism link of the split projection. Kind: PROVED. -/
def ILStageStepFamilyLinked.ofAssembled {Z₀ Z₁ : TwoTermStage ι} (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : AssembledLimit a U hU Cn hW) (hL : L.Realized)
    (rla : RetainedLocalArithmetic U L.C L.D) (h02 : RetainedZeroTwo rla)
    (hJ : rla.JAt P = conjMatrix Cn W hW P)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C)
      (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P L.C)
      (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁)
    (hproj : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i],
      QuasiIso (GHom.toCC (L.stages i).projection)) :
    ILStageStepFamilyLinked P Cn W hW Z₀ Z₁ where
  hS := hS
  α := α
  Fam := Fam
  hOld := a.oldFlat
  hres := a.residualSupport.residual_finite p hS h2
  B := max L.bound (a.residualSupport.producerBounds p hK hS h2).choose
  hbdd := (a.residualSupport.producerBounds p hK hS h2).choose_spec.1
  hB i _ n := le_trans ((a.residualSupport.producerBounds p hK hS h2).choose_spec.2 i n)
    (le_max_right _ _)
  Uq := _
  ιq := _
  stages := L.stages
  U := U
  hU := hU
  C := L.C
  D := L.D
  E := L.E
  hlift := L.local_lift
  hrank := L.residual_ranks
  hrankB n := le_trans (L.rank_bound n) (le_max_left _ _)
  rla := rla
  h02 := h02
  hJ := hJ
  hdet := hdet
  φ := φ
  φ' := φ'
  projection_model := hproj
  realized := hL

/-- **The linked inputs from the RC53 group's arithmetic inputs**: with the realized support-change
assembly on the stages chosen together with their local retractions
(`assemble_from_support_change_realized_model`), there is an assembled limit `L` such that every
retained local arithmetic on it with its zero/two realization and `J = ρ_T(τ)`, together with the
detection and the side-to-stage isomorphisms, gives linked inputs; the projection link comes from
the retractions (`projection_model_of_homotopyEquiv`). Kind: PROVED. -/
theorem exists_linked_of_support_change (Z₀ Z₁ : TwoTermStage ι) (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Pr : ActualSupportPresentation Fam R) (oldFlat : Fam.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput Fam O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ∃ T : ResidualSupportControl Fam R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs Fam O R 6) U hU Cn hW,
        ∀ (rla : RetainedLocalArithmetic U L.C L.D), RetainedZeroTwo rla →
          rla.JAt P = conjMatrix Cn W hW P →
          finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
            (limitRelaxed (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).U →
          ((selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀) →
          ((selCx (singularLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) →
          Nonempty (ILStageStepFamilyLinked P Cn W hW Z₀ Z₁) := by
  obtain ⟨T, L, -, hL, hproj⟩ :=
    ZInQ.Manuscript.RC.Wiring.assemble_from_support_change_realized_model
      p h788 hK hS h2 Pr oldFlat stage U hU Cn hW
  refine ⟨T, L, fun rla h02 hJ hdet φ φ' => ⟨ILStageStepFamilyLinked.ofAssembled p hK hS h2 L hL
    rla h02 hJ hdet φ φ' ?_⟩⟩
  exact projection_model_of_homotopyEquiv (fun i => (L.stages i).projection) U hproj

end Assembled

/-! **The switching inputs on the stage family** -/

section Switch

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Inner-limit switching inputs on the stage family of the text** (tex 4385–4451, 4976–5195,
5027–5086): the frame over `Λ_𝔭` and, at each reached configuration with fiber dimension `> 1`, a
successor with a coordinate step and a linked switch on the stage family
(`ILStageStepFamilyLinked`) whose limit sides' Selmer complexes are homotopy equivalent to the
fibres of the configuration and of its successor (over `k(𝔭)`; given the frame, equivalently to
the stages' two-term fibre complexes: isomorphic cohomology in every degree, with no compatibility
with the step's maps). Kind: definition (inputs). -/
structure InnerLimitSwitchFamily (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The linked family switches, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepFamilyLinked P Cn W hW (stage c) (stage (Φ.next c p)),
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {P Cn W hW} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **The inner-limit inputs of the family inputs** (each step through its step data). Kind:
PROVED. -/
def InnerLimitSwitchFamily.toInner (X : InnerLimitSwitchFamily P Cn W hW Φ ι u) :
    InnerLimitSwitchModel P Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.stepData, hF, hS⟩

/-- **Regularity from the family inputs at a height-one prime**. Kind: PROVED (from the
inputs). -/
theorem regular_of_innerLimitSwitchFamily (hP : P.height = 1) (hι : Function.Injective ι)
    (X : InnerLimitSwitchFamily P Cn W hW Φ ι u) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchModel hP hι X.toInner

end Switch

end ZInQ.Manuscript.RC.Wiring
