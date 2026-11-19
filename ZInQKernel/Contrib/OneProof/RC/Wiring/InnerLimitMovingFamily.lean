import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageFamily
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.StageLinks

/-!
**Theorem 5.3, Lane RC0 round 16: the switch inputs on moving supports.**

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5195), with the switch
at a derivative label on the inner-limit objects (tex 4385–4451, 4834–4907, 5027–5086).

**Moving supports** (tex 2727–2741, 4255–4280). The stage characters `χ_h Ψ_i` are ramified at a
moving conductor prime `r_i` that varies with the precision `i`. They are built separately at each
coefficient stage and need not be restrictions of one character, so the support of the stage
character grows with `i`: at stage `i` it contains the earlier support, `r_i` and the previous
derivative labels. The RC53 group's `ActualStageFamily S₀ W α` fixes one finite old support `S₀`
and characters `α i` of `G_{K,S₀}`. An injective sequence of conductor primes cannot lie in one
finite set, so that family cannot carry the characters of the text. Below the old support is a
function of the stage.

* `MovingStageFamily W`: finite old supports `oldSupport i`, characters `α i` of
  `G_{K, oldSupport i}`, new primes `q i ∉ oldSupport i` of odd residue characteristic, and the old
  conditions in the coefficient model of the enlarged support. Per stage, as for the RC53 group's
  family: `support`, `character`, `coefficient`, `conditions`, `datum`, `globalCx`, `localCx`,
  `restriction`, `stageRes`. PROVED: `fullTorsion` (from the per-stage hypothesis
  `FullTorsionAt`), `old_free`, `flat` (every stage complex has flat terms).
* `ILStageStepMoving`: the inputs of one switch on a moving family, with the split-stage data in
  the generic shape of `ILStageStep`. PROVED: `ILStageStepMoving.toILStageStep` (the residue
  identity of tex 5037 by `RetainedLocalArithmetic.hloc_at_conj`). `ILStageStepMovingLinked` adds
  the links of `ILStageStepFamilyLinked`, and `InnerLimitSwitchMoving` is the switching frame with
  moving switches. PROVED: `InnerLimitSwitchMoving.toInner`, `regular_of_innerLimitSwitchMoving`.
* `exists_linked_moving`: the RC53 group's realized stage producer takes arbitrary stage
  complexes, so on moving supports it gives the retained data and their realization from the
  family, its residual package, the per-stage split data and the projection link. PROVED.
* The per-stage split data on moving supports, as for the RC53 group's fixed support, stage by
  stage: `MovingOldDualityData`, `MovingStageArithmeticInput`, `MovingSplitStage`,
  `MovingLinkedSplitStage`, `MovingArithmeticInputs` (data and inputs). PROVED:
  `MovingOldDualityData.exists_original_trace_duality`,
  `MovingStageArithmeticInput.exists_linked_split`, `producedStagesMoving'` with its projection
  links, and `exists_linked_of_moving_inputs` (linked moving inputs from the moving arithmetic
  inputs, the retained local arithmetic, the detection and the side-to-stage isomorphisms).
* The fixed support is the constant case. PROVED: `MovingStageFamily.ofActual`, whose stage data
  are those of the fixed-support family by `rfl`; `ILStageStepFamily.toMoving`, with
  `X.toMoving.toILStageStep = X.toILStageStep` by `rfl`; `ILStageStepFamilyLinked.toMovingLinked`
  and `InnerLimitSwitchFamily.toMoving`; for the producers' inputs `MovingOldDualityData.ofActual`
  and `MovingStageArithmeticInput.ofActual`.

The actual conjugation `Cn : ActualConj K S` keeps its own support `S`, as in the fixed-support
file; `S` need not be any old support. The residual package on moving supports
(`MovingResidualPackage`) is an input here; its production by a change of support is not stated.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  conjMatrix transportedPairing localPairingOfMat splitSelData stageLocMat stagePairingInputOfSel
  compactSpace_Gloc stageA_isNilpotent_maximalIdeal stageA_zero_subsingleton)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal flat_module_free)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide Vec2)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite flat_selmerCochains)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer CondAt Mcoef fullAt zeroAt FullTorsion)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap selData LocalConditions natHom
  resCochains)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients (characterAfterSupport
  fullTorsion_afterSupport)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (actualStageLocalCx)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (ActualStageFamily SplitStage
  stageRes flat_over_zeroRing RetainedStageRealization exists_retained_of_stageInputs_realized)
open ZInQ.Contrib.RC53Assist.ResidueIdentity (RetainedLocalArithmetic RetainedZeroTwo)

/-! **The stage family on moving supports** -/

section MovingFamily

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The stage family on moving supports** (tex 2727–2741, 4255–4280, 4401–4406, 4809–4830,
5055–5059). At stage `i`:
* `oldSupport i`, `oldFinite`: the finite old support of the stage; it contains the conductor
  prime `r_i` of the stage character and the previous derivative labels (data);
* `α i`, `openα`: the stage character `χ_h Ψ_i` of `G_{K, oldSupport i}`, with open kernel
  (data and ELLIOT);
* `q i`, `new`, `odd`: the new derivative prime, outside the old support of its stage, of odd
  residue characteristic (data and GLUE);
* `old i v`: the condition at an old place `v`, in the coefficient model of the enlarged support
  `insert (q i) (oldSupport i)` (data).
With a constant old support this is the RC53 group's `ActualStageFamily` (`ofActual`).
Kind: definition (inputs). -/
structure MovingStageFamily where
  /-- The old support at stage `i`. -/
  oldSupport : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- Each old support is finite. -/
  oldFinite : ∀ i, (oldSupport i).Finite
  /-- The stage characters. -/
  α : ∀ i, GKS K (oldSupport i) →* (Acoef i)ˣ
  /-- The stage characters have open kernels. -/
  [openα : ∀ i, IsOpenKer (α i)]
  /-- The new derivative prime at stage `i`. -/
  q : ℕ → HeightOneSpectrum (𝓞 K)
  /-- It is not in the old support of its stage. -/
  new : ∀ i, q i ∉ oldSupport i
  /-- It has odd residue characteristic. -/
  odd : ∀ i, (2 : 𝓞 K) ∉ (q i).asIdeal
  /-- The old conditions, in the coefficient model of the enlarged support. -/
  old : ∀ i (v : Places K (oldSupport i)),
    CondAt K (insert (q i) (oldSupport i)) (Acoef i)
      (Mcoef K (insert (q i) (oldSupport i)) W i
        (characterAfterSupport (Set.subset_insert (q i) (oldSupport i)) i (α i)))
      ⟨v.1, Or.inr v.2⟩

attribute [instance] MovingStageFamily.openα

variable {W}

/-- The enlarged support `insert (q i) (oldSupport i)` of stage `i` (tex 4809–4830).
Kind: definition. -/
abbrev MovingStageFamily.support (F : MovingStageFamily W) (i : ℕ) :=
  insert (F.q i) (F.oldSupport i)

omit [W.IsElliptic] in
/-- The old support of a stage lies in its enlarged support. Kind: PROVED. -/
theorem MovingStageFamily.inclusion (F : MovingStageFamily W) (i : ℕ) :
    F.oldSupport i ⊆ F.support i := Set.subset_insert (F.q i) (F.oldSupport i)

/-- The stage character on the enlarged support (tex 2781–2796, 4809–4830). Kind: definition. -/
abbrev MovingStageFamily.character (F : MovingStageFamily W) (i : ℕ) :=
  characterAfterSupport (F.inclusion i) i (F.α i)

/-- The coefficient module `M_i` on the enlarged support (tex 2726, 4385–4388).
Kind: definition. -/
abbrev MovingStageFamily.coefficient (F : MovingStageFamily W) (i : ℕ) :=
  Mcoef K (F.support i) W i (F.character i)

/-- The old local conditions, indexed by the old places of the stage (tex 4385–4388, 5055–5059).
Kind: definition. -/
def MovingStageFamily.conditions (F : MovingStageFamily W) (i : ℕ) :
    LocalConditions (Acoef i) (GKS K (F.support i))
      (fun v : Places K (F.oldSupport i) => Gloc K v.1)
      (fun v => locMap K (F.support i) v.1) (F.coefficient i) where
  U v := (F.old i v).U
  i v := (F.old i v).i

/-- The stage Selmer datum, with conditions at the old places only; the new prime carries no
condition (tex 4385–4388, 4401–4406, 5055–5065). Kind: definition. -/
def MovingStageFamily.datum (F : MovingStageFamily W) (i : ℕ) : SelData (Acoef i) :=
  selData (Acoef i) (GKS K (F.support i)) (fun v : Places K (F.oldSupport i) => Gloc K v.1)
    (fun v => locMap K (F.support i) v.1) (F.coefficient i) (F.conditions i)

/-- The stage complex (tex 4385–4388, 4391–4406). Kind: definition. -/
abbrev MovingStageFamily.globalCx (F : MovingStageFamily W) (i : ℕ) :=
  selCx (F.datum i)

/-- The local cochains at the new prime, with the restricted coefficient module
(tex 4859–4868). Kind: definition. -/
abbrev MovingStageFamily.localCx (F : MovingStageFamily W) (i : ℕ) :=
  actualStageLocalCx W i (F.character i) (F.q i)

/-- Restriction of the global cochains to the new prime (tex 4859–4868). Kind: definition. -/
def MovingStageFamily.restriction (F : MovingStageFamily W) (i : ℕ) :
    GHom (F.datum i).G (F.localCx i) :=
  natHom (resCochains (k := Acoef i) (M := F.coefficient i)
    (locMap K (F.support i) (F.q i)))

/-- The localization into the split model: the projection of the Selmer complex, the restriction
and a split projection `p` (tex 4385–4388, 4859–4868). Kind: definition. -/
def MovingStageFamily.stageRes (F : MovingStageFamily W) (i : ℕ)
    (p : GHom (F.localCx i) (splitLocalComplex (Acoef i))) :
    GHom (F.globalCx i) (splitLocalComplex (Acoef i)) :=
  ghomComp (ghomComp (projG (F.datum i)) (F.restriction i)) p

/-- Full `2^i`-torsion over the old support of every stage (tex 2725–2727).
Kind: definition (hypothesis). -/
def MovingStageFamily.FullTorsionAt (F : MovingStageFamily W) : Prop :=
  ∀ i, FullTorsion K (F.oldSupport i) W (2 ^ i)

/-- The enlarged support of each stage keeps the full torsion (tex 2725–2727, 4809–4830).
Kind: PROVED. -/
theorem MovingStageFamily.fullTorsion (F : MovingStageFamily W) (hT : F.FullTorsionAt)
    (i : ℕ) : FullTorsion K (F.support i) W (2 ^ i) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  exact fullTorsion_afterSupport (F.inclusion i) W (2 ^ i) (hT i)

omit [W.IsElliptic] in
/-- Full two-power torsion over every old support gives `FullTorsionAt`. Kind: PROVED. -/
theorem MovingStageFamily.fullTorsionAt_of_hasFullTwoTorsion (F : MovingStageFamily W)
    (h : ∀ i, HasFullTwoTorsion K (F.oldSupport i) W) : F.FullTorsionAt :=
  fun i => (h i).full i

/-- Full two-power torsion over a support contained in every old support gives `FullTorsionAt`:
the torsion persists in larger supports. Kind: PROVED. -/
theorem MovingStageFamily.fullTorsionAt_of_subset (F : MovingStageFamily W)
    {S : Set (HeightOneSpectrum (𝓞 K))} [HasFullTwoTorsion K S W]
    (hS : ∀ i, S ⊆ F.oldSupport i) : F.FullTorsionAt := by
  intro i
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  exact fullTorsion_afterSupport (hS i) W (2 ^ i) (HasFullTwoTorsion.full i)

/-- Flat terms of the old conditions other than zero and full, at positive stages
(tex 4391–4414). Kind: definition (GLUE input). -/
def MovingStageFamily.NontrivialOldFlat (F : MovingStageFamily W) : Prop :=
  ∀ i [NeZero i] (v : Places K (F.oldSupport i)),
    F.old i v ≠ fullAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩ →
    F.old i v ≠ zeroAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩ →
    ∀ n : ℤ, Module.Flat (Acoef i) ((F.old i v).U.X n)

/-- The old conditions have free terms at positive stages: the zero and full conditions
directly, the others from `NontrivialOldFlat`, the maximal ideal of `A_i` being nilpotent
(tex 4391–4414). Kind: PROVED. -/
theorem MovingStageFamily.old_free (F : MovingStageFamily W) (hT : F.FullTorsionAt)
    (hOld : F.NontrivialOldFlat) (i : ℕ) [NeZero i] (v : Places K (F.oldSupport i)) (n : ℤ) :
    Module.Free (Acoef i) ((F.old i v).U.X n) := by
  have hnil := stageA_isNilpotent_maximalIdeal i
  have : Module.Free (Acoef i) (F.coefficient i) :=
    mcoef_free W i (F.character i) (F.fullTorsion hT i)
  have : Module.Flat (Acoef i) (F.coefficient i) := inferInstance
  by_cases hF : F.old i v =
      fullAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩
  · rw [hF]
    exact fullAt_free hnil (F.coefficient i) _ n
  · by_cases hZ : F.old i v =
        zeroAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩
    · rw [hZ]
      exact zeroAt_free (F.coefficient i) _ n
    · have : Module.Flat (Acoef i) ((F.old i v).U.X n) := hOld i v hF hZ n
      exact flat_module_free hnil

/-- **Every stage complex has flat terms** (tex 4391–4414): at stage zero the coefficient ring is
zero; at a positive stage by flatness of the continuous Selmer cochains, the old support
`oldSupport i` being finite. Kind: PROVED. -/
theorem MovingStageFamily.flat (F : MovingStageFamily W) (hT : F.FullTorsionAt)
    (hOld : F.NontrivialOldFlat) :
    ∀ i n, Module.Flat (StageA i) ((F.globalCx i).X n) := by
  intro i n
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have : Subsingleton (StageA 0) := stageA_zero_subsingleton
    exact flat_over_zeroRing (StageA 0) ((F.globalCx 0).X n)
  · have : NeZero i := ⟨by omega⟩
    let : Fintype (Places K (F.oldSupport i)) := (F.oldFinite i).fintype
    have : ∀ v : Places K (F.oldSupport i), CompactSpace (Gloc K v.1) :=
      fun v => compactSpace_Gloc v.1
    have : Module.Free (Acoef i) (F.coefficient i) :=
      mcoef_free W i (F.character i) (F.fullTorsion hT i)
    have : Module.Flat (Acoef i) (F.coefficient i) := inferInstance
    exact flat_selmerCochains (stageA_isNilpotent_maximalIdeal i)
      (GKS K (F.support i)) (fun v : Places K (F.oldSupport i) => Gloc K v.1)
      (fun v => locMap K (F.support i) v.1) (F.coefficient i)
      (F.conditions i) (F.old_free hT hOld i) n

end MovingFamily

/-! **The inputs of one switch on a moving family** -/

section Step

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The inputs of one switch on a moving stage family** (tex 2727–2741, 4255–4280, 4385–4451,
4834–4907, 5027–5086). As `ILStageStepFamily`, on a `MovingStageFamily`:
* `Fam`, `hFull`, `hOld`: the moving stage family, full torsion over its old supports, and flat
  terms of its old conditions other than zero and full (data, ELLIOT and GLUE);
* `hres`, `B`, `hbdd`, `hB`: finite residual cohomology of the moving stage complexes, the range
  `[0, 3]` and a uniform bound (ELLIOT, tex 4401–4406);
* `Uq`, `ιq`, `p`, `Q`, `tr`, `htr`, `hdual`: the condition at the derivative label, a split
  projection of the local cochains at the new prime, the self-paired split Selmer datum whose
  localization is `stageRes` (projection, restriction, `p`), its trace and the global-duality
  quasi-isomorphism (GLUE, tex 4385–4451, 4859–4873);
* `U`, `hU`, `C`, `D`, `E`, `hlift`, `hrank`, `hrankB`: the ultrafilter and a retained realization
  (data, tex 4385–4451);
* `rla`, `h02`, `hJ`: the retained local arithmetic at the derivative label, its zero/two
  realization and the identification of its conjugation matrix with `ρ_T(τ)` (GLUE, tex
  4860–4863, 5027–5043); the residue identity of tex 5037 is PROVED from them;
* `hdet`: the detection `F ≤ U` (GLUE, tex 5055–5072);
* `φ`, `φ'`: the side-to-stage isomorphisms (GLUE, tex 5040–5054).
The actual conjugation `Cn` keeps its own support `S`. Kind: definition (inputs). -/
structure ILStageStepMoving (Z₀ Z₁ : TwoTermStage ι) where
  /-- The moving stage family. -/
  Fam : MovingStageFamily W
  /-- Full torsion over the old support of every stage. -/
  hFull : Fam.FullTorsionAt
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
  /-- The split projection of the local cochains. -/
  p : ∀ i, GHom (Fam.localCx i) (splitLocalComplex (Acoef i))
  /-- The self-paired split Selmer datum. -/
  Q : ∀ i, SelPairData
    (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i)))
    (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i)))
  /-- The trace. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[Acoef i] Acoef i
  /-- The trace kills coboundaries. -/
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- The split global duality. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
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
  hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
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

variable {P Cn W hW}

/-- **`ILStageStep` from the inputs on a moving family**: the stage complexes are the family's,
their localization is `stageRes` with the split projection `p`, `hflat` is
`MovingStageFamily.flat`, and the residue identity is `RetainedLocalArithmetic.hloc_at_conj`
(`ε₀ = −ε`, `ε₂ = ε`, `σ = 1`). Kind: PROVED. -/
def ILStageStepMoving.toILStageStep {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepMoving P Cn W hW Z₀ Z₁) : ILStageStep P Cn W hW Z₀ Z₁ where
  U := X.U
  hU := X.hU
  G := X.Fam.globalCx
  hflat := X.Fam.flat X.hFull X.hOld
  Uc := X.Uq
  res i := X.Fam.stageRes i (X.p i)
  ιc i := ghomComp (X.ιq i) (X.p i)
  Q := X.Q
  tr := X.tr
  htr := X.htr
  hdual := X.hdual
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

/-- The inner-limit step data of the inputs on a moving family. Kind: definition. -/
abbrev ILStageStepMoving.stepData {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepMoving P Cn W hW Z₀ Z₁) : InnerLimitStepData P Z₀ Z₁ :=
  X.toILStageStep.toStepData

variable (P Cn W hW) in
/-- **The inputs of one switch on a moving family, with their links** (tex 4385–4451, 4859–4868),
as `ILStageStepFamilyLinked`: at the retained precision the split projection is a
quasi-isomorphism onto the split model, and on a `U`-large set of positive stages the retained
data are realized on the moving stage complexes (the RC53 group's `RetainedStageRealization`).
Kind: definition (inputs). -/
structure ILStageStepMovingLinked (Z₀ Z₁ : TwoTermStage ι) extends
    ILStageStepMoving P Cn W hW Z₀ Z₁ where
  /-- At the retained precision the split projection is a quasi-isomorphism. -/
  projection_model : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], QuasiIso (GHom.toCC (p i))
  /-- The retained data are realized on the moving stage complexes. -/
  realized : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], Nonempty
    (RetainedStageRealization C D i (stagePairingInputOfSel (Q i) (tr i) (htr i)))

end Step

/-! **The retained realization on moving supports** -/

section Realization

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The retained realization of moving stage data** (tex 4385–4451): the RC53 group's realized
stage producer `exists_retained_of_stageInputs_realized` takes arbitrary stage complexes, so it
applies to the moving stage complexes verbatim, with flat terms by `MovingStageFamily.flat`. From
the moving family, its residual package, the per-stage split data and the projection link there
are retained data `C`, `D` such that every retained local arithmetic on them with its zero/two
realization and `J = ρ_T(τ)`, together with the detection and the side-to-stage isomorphisms,
gives linked moving inputs. Only the per-stage split data and the residual package remain to be
produced on moving supports. Kind: PROVED. -/
theorem exists_linked_moving (Z₀ Z₁ : TwoTermStage ι) (Fam : MovingStageFamily W)
    (hFull : Fam.FullTorsionAt) (hOld : Fam.NontrivialOldFlat)
    (hres : ∀ i [NeZero i], ResidualCohomologyFinite (Fam.globalCx i)) (B : ℕ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (Fam.globalCx i) n) = 0)
    (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (Fam.globalCx i) n) ≤ B)
    (Uq : ∀ i, GCx (Acoef i)) (ιq : ∀ i, GHom (Uq i) (Fam.localCx i))
    (p : ∀ i, GHom (Fam.localCx i) (splitLocalComplex (Acoef i)))
    (Q : ∀ i, SelPairData
      (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i)))
      (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i))))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i))))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (hproj : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], QuasiIso (GHom.toCC (p i))) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C),
      ∀ rla : RetainedLocalArithmetic U C D, RetainedZeroTwo rla →
        rla.JAt P = conjMatrix Cn W hW P →
        finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
          (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U →
        ((selCx (finiteLimitSide (fibreLimitGlobal U hU P C)
          (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀) →
        ((selCx (singularLimitSide (fibreLimitGlobal U hU P C)
          (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) →
        Nonempty (ILStageStepMovingLinked P Cn W hW Z₀ Z₁) := by
  obtain ⟨r₀, C, D, E, hrank, -, -, hr₀B, hev, hloc, hreal⟩ :=
    exists_retained_of_stageInputs_realized U hU (fun i => Fam.globalCx i)
      (Fam.flat hFull hOld) Uq (fun i => Fam.stageRes i (p i))
      (fun i => ghomComp (ιq i) (p i)) Q tr htr hdual hres 0 3 hbdd B hB
  have hrank' : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
      C.rank n = Module.finrank (ResidueField (StageA i))
        (residualCohomologyAt (Fam.globalCx i) n) := by
    filter_upwards [hev] with i hi
    intro _ n
    rw [hrank]
    exact hi n
  have hrankB' : ∀ n, C.rank n ≤ B := fun n => hrank ▸ hr₀B n
  exact ⟨C, D, fun rla h02 hJ hdet φ φ' =>
    ⟨{ Fam := Fam, hFull := hFull, hOld := hOld, hres := hres, B := B, hbdd := hbdd, hB := hB,
       Uq := Uq, ιq := ιq, p := p, Q := Q, tr := tr, htr := htr, hdual := hdual, U := U,
       hU := hU, C := C, D := D, E := E, hlift := hloc, hrank := hrank', hrankB := hrankB',
       rla := rla, h02 := h02, hJ := hJ, hdet := hdet, φ := φ, φ' := φ',
       projection_model := hproj, realized := hreal }⟩⟩

end Realization

/-! **The per-stage split data on moving supports** -/

section MovingProducers

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.ResidualFiniteness ZInQ.Contrib.RC53Assist.ResidualBounds
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
open ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (GRetract)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange
open scoped Classical

/-- The discrete topology of the finite coefficient stages, as for the fixed-support producers
(tex 4391–4414). Kind: definition. -/
local instance movingStageTopology (i : ℕ) : TopologicalSpace (Acoef i) := acoefTop i

/-- The finite coefficient topology is discrete (tex 4391–4414). Kind: PROVED. -/
local instance movingStageDiscrete (i : ℕ) : DiscreteTopology (Acoef i) := acoefTop_discrete i

section OldDuality

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]

/-- **The old duality data on moving supports** (as the RC53 group's `OldDualityData`, per stage;
tex 2725–2760, 3500–3506, 5055–5071): full torsion over every old support, the old quadratic
generator of the fixed parameter in the field of each old support, the Kummer places of each
stage with the character dictionary, the roots of unity, the previous derivative labels (old at
their stage) with their conditions, and the original old conditions.
Kind: definition (data, GLUE and ELLIOT). -/
structure MovingOldDualityData (F : MovingStageFamily W) where
  /-- Full torsion over every old support. -/
  full : F.FullTorsionAt
  /-- The old quadratic generator at each stage. -/
  root : ∀ i, KS K (F.oldSupport i)
  /-- The old quadratic parameter. -/
  parameter : K
  /-- The quadratic relation. -/
  square : ∀ i, root i ^ 2 = algebraMap K (KS K (F.oldSupport i)) parameter
  /-- The generator is nonzero. -/
  nonzero : ∀ i, root i ≠ 0
  /-- The primitive Kummer places of each stage. -/
  kummerPlaces : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- The old character dictionary. -/
  locallyQuadratic : ∀ i [NeZero i], ∀ v ∈ kummerPlaces i,
    IsLocallyQuadAt i (F.α i) (quadChar (root i) (square i) (nonzero i)) v
  /-- The roots of unity over each old support. -/
  roots : ∀ i [NeZero i], HasRootsOfUnity K (F.oldSupport i) (2 ^ i)
  /-- The previous derivative labels at each stage. -/
  derivatives : ∀ i, Finset (Places K (F.support i))
  /-- They are old at their stage. -/
  derivative_old : ∀ i v, v ∈ derivatives i → v.1 ∈ F.oldSupport i
  /-- The first old derivative condition. -/
  derivativeA : ∀ i [NeZero i] (v : Places K (F.support i)), v ∈ derivatives i →
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v
  /-- The second old derivative condition. -/
  derivativeB : ∀ i [NeZero i] (v : Places K (F.support i)), v ∈ derivatives i →
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (F.α i))) v
  /-- The original first old conditions. -/
  originalOldA : ∀ i [NeZero i] (v : Places K (F.support i)),
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v
  /-- The original second old conditions. -/
  originalOldB : ∀ i [NeZero i] (v : Places K (F.support i)),
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (F.α i))) v

variable {F : MovingStageFamily W} (O : MovingOldDualityData F) (i : ℕ) [NeZero i]

/-- Original first conditions, full at the new prime (tex 4385–4388, 5055–5071).
Kind: definition. -/
def MovingOldDualityData.oldA (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v :=
  if v.1 = F.q i then fullAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v
  else O.originalOldA i v

/-- Original second conditions, zero at the new prime (tex 4385–4388, 5055–5071).
Kind: definition. -/
def MovingOldDualityData.oldB (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (F.α i))) v :=
  if v.1 = F.q i then zeroAt K (F.support i) (Acoef i)
    (MinS (F.inclusion i) W i (charInv (F.α i))) v
  else O.originalOldB i v

/-- First conditions with the old derivative conditions retained (tex 5055–5059).
Kind: definition. -/
def MovingOldDualityData.atA (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v :=
  if hv : v ∈ O.derivatives i then O.derivativeA i v hv else O.oldA i v

/-- Second conditions with the old derivative conditions retained (tex 5055–5059).
Kind: definition. -/
def MovingOldDualityData.atB (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (F.α i))) v :=
  if hv : v ∈ O.derivatives i then O.derivativeB i v hv else O.oldB i v

/-- The original first arithmetic conditions (tex 5055–5071). Kind: definition. -/
def MovingOldDualityData.conditionsA :
    GaloisLocalConditions K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) :=
  ofCondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) (O.atA i)

/-- The original second arithmetic conditions (tex 5055–5071). Kind: definition. -/
def MovingOldDualityData.conditionsB :
    GaloisLocalConditions K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (F.α i))) :=
  ofCondAt K (F.support i) (Acoef i)
    (MinS (F.inclusion i) W i (charInv (F.α i))) (O.atB i)

/-- The original inflated Weil pairing (tex 4385–4388, 5035–5071). Kind: definition. -/
abbrev MovingOldDualityData.coefficientPair :=
  actLBeta (F.inclusion i) W i (F.α i) (O.roots i)

/-- Original isotropy data (tex 4385–4388, 5055–5071). Kind: definition. -/
abbrev MovingOldDualityData.Isotropy :=
  GaloisTruncIsotropyData K (F.support i) (Acoef i) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i)

/-- The original paired Galois-cochain diagram (tex 4385–4388, 5035–5071). Kind: definition. -/
abbrev MovingOldDualityData.pair (I : O.Isotropy i) :=
  galoisPairDataT K (F.support i) (Acoef i) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I

/-- Canonical first old conditions (tex 5055–5059). Kind: definition. -/
abbrev MovingOldDualityData.canonicalOldA (v : Places K (F.support i)) :=
  actLCondA (F.inclusion i) W i (O.root i) (O.square i) (O.nonzero i)
    (O.full i) (O.kummerPlaces i) (F.α i) (O.locallyQuadratic i) v

/-- Canonical second old conditions (tex 5055–5059). Kind: definition. -/
abbrev MovingOldDualityData.canonicalOldB (v : Places K (F.support i)) :=
  actLCondB (F.inclusion i) W i (O.root i) (O.square i) (O.nonzero i)
    (O.full i) (O.kummerPlaces i) (F.α i) (O.locallyQuadratic i) v

/-- Old pairs with a supplied complement theorem (tex 2813–2814, 5055–5071).
Kind: definition. -/
def MovingOldDualityData.KnownOldPair (v : Places K (F.support i)) : Prop :=
  (O.oldA i v = O.canonicalOldA i v ∧ O.oldB i v = O.canonicalOldB i v) ∨
  (O.oldA i v = fullAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v ∧
    O.oldB i v = zeroAt K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (F.α i))) v) ∨
  (O.oldA i v = zeroAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (F.α i)) v ∧
    O.oldB i v = fullAt K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (F.α i))) v) ∨
  (O.oldA i v = derivativeStrictAt v ∧ O.oldB i v = derivativeRelaxedAt v)

/-- The complement input for the other old pairs (tex 5055–5071). Kind: definition (GLUE). -/
def MovingOldDualityData.OtherOldComplements : Prop :=
  ∀ (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)), ¬ O.KnownOldPair i v →
    ∀ (J : LocalTruncIsotropy (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)),
      QuasiIso (GHom.toCC (orthLocalMap (O.oldA i v).i (O.oldB i v).i
        (orthGaloisPair K (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
        J (L.trv v) (L.htrv₁ v)))

/-- The complement input for the other old derivative conditions (tex 5055–5071).
Kind: definition (GLUE). -/
def MovingOldDualityData.OtherDerivativeComplements : Prop :=
  ∀ (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) (hv : v ∈ O.derivatives i),
    (O.derivativeA i v hv ≠ derivativeStrictAt v ∨
      O.derivativeB i v hv ≠ derivativeRelaxedAt v) →
    ∀ (J : LocalTruncIsotropy (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)),
      QuasiIso (GHom.toCC (orthLocalMap
        (O.derivativeA i v hv).i (O.derivativeB i v hv).i
        (orthGaloisPair K (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
        J (L.trv v) (L.htrv₁ v)))

/-- Full local duality at each place of the enlarged support of stage `i` (tex 5055–5071).
Kind: PROVED. -/
theorem MovingOldDualityData.full_local_duality (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) :
    QuasiIso (GHom.toCC (adjHom (orthGaloisPair K (O.coefficientPair i)
      (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
      2 (L.trv v) (L.htrv₁ v))) := by
  have : Finite (MinS (F.inclusion i) W i (F.α i)) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (F.α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (F.α i))) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (charInv (F.α i))))
  exact p.localDuality (F.support i) 2 (Acoef i)
    (nekovarFiniteSetting_acoef K hK (F.support i) ((F.oldFinite i).insert (F.q i))
      (fun v hv => F.inclusion i (h2 v hv)) i)
    (MinS (F.inclusion i) W i (F.α i)) (MinS (F.inclusion i) W i (charInv (F.α i)))
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (weilPairingM_bijective W (O.roots i) (Acoef i) (F.α i) (O.full i))
    (weilPairingM_flip_bijective W (O.roots i) (Acoef i) (F.α i) (O.full i))
    (cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i))
    v (L.trv v) (L.htrv₁ v) (L.iso v)

/-- The old complements: the supplied cases, and `OtherOldComplements` otherwise
(tex 5055–5071). Kind: PROVED. -/
theorem MovingOldDualityData.old_complement (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (hOther : O.OtherOldComplements i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i))
    (J : LocalTruncIsotropy (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
      J (L.trv v) (L.htrv₁ v))) := by
  by_cases hstd : O.oldA i v = O.canonicalOldA i v ∧ O.oldB i v = O.canonicalOldB i v
  · exact actLPerf_congr _ _ hstd.1 hstd.2 (L.trv v) (L.htrv₁ v)
      (fun J' => actLPerf (F.inclusion i) W i (O.root i) (O.square i) (O.nonzero i)
        (O.full i) (O.kummerPlaces i) (F.α i) (O.roots i)
        (O.locallyQuadratic i) L.trv L.htrv₁ p.localKummer p.localDuality
        p.unramifiedDuality hK ((F.oldFinite i).insert (F.q i)) (F.oldFinite i) h2 L.iso v
        J') J
  · by_cases hFZ : O.oldA i v = fullAt K (F.support i) (Acoef i)
        (MinS (F.inclusion i) W i (F.α i)) v ∧
        O.oldB i v = zeroAt K (F.support i) (Acoef i)
          (MinS (F.inclusion i) W i (charInv (F.α i))) v
    · exact actLPerf_congr _ _ hFZ.1 hFZ.2 (L.trv v) (L.htrv₁ v)
        (actLPerf_full_zero _ _ v (L.trv v) (L.htrv₁ v)) J
    · by_cases hZF : O.oldA i v = zeroAt K (F.support i) (Acoef i)
          (MinS (F.inclusion i) W i (F.α i)) v ∧
          O.oldB i v = fullAt K (F.support i) (Acoef i)
            (MinS (F.inclusion i) W i (charInv (F.α i))) v
      · exact actLPerf_congr _ _ hZF.1 hZF.2 (L.trv v) (L.htrv₁ v)
          (fun J' => zero_full_complement
            (orthGaloisPair K (O.coefficientPair i)
              (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
            (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK h2 L v)) J
      · by_cases hSR : O.oldA i v = derivativeStrictAt v ∧
            O.oldB i v = derivativeRelaxedAt v
        · have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
          exact actLPerf_congr _ _ hSR.1 hSR.2 (L.trv v) (L.htrv₁ v)
            (fun J' => derivativeAt_local_complement (O.coefficientPair i)
              (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v
              (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK h2 L v)) J
        · exact hOther L v (fun h => h.elim hstd
            (fun h => h.elim hFZ (fun h => h.elim hZF hSR))) J

/-- The old derivative complements (tex 5055–5071). Kind: PROVED. -/
theorem MovingOldDualityData.derivative_complement (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (hOther : O.OtherDerivativeComplements i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) (hv : v ∈ O.derivatives i)
    (J : LocalTruncIsotropy (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v)
      J (L.trv v) (L.htrv₁ v))) := by
  by_cases hA : O.derivativeA i v hv = derivativeStrictAt v
  · by_cases hB : O.derivativeB i v hv = derivativeRelaxedAt v
    · have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
      exact actLPerf_congr _ _ hA hB (L.trv v) (L.htrv₁ v)
        (fun J' => derivativeAt_local_complement (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i)) v
          (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK h2 L v)) J
    · exact hOther L v hv (Or.inr hB) J
  · exact hOther L v hv (Or.inl hA) J

/-- Old-condition orthogonality, place by place (tex 5055–5071). Kind: PROVED. -/
theorem MovingOldDualityData.local_complements [Fintype (Places K (F.support i))]
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (hOld : O.OtherOldComplements i)
    (hOther : O.OtherDerivativeComplements i) (I : O.Isotropy i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0)
    (hN : L.Normalizes tr) :
    QuasiIso (GHom.toCC (localDualityMap (O.pair i I) tr htr)) := by
  apply orthogonalComplementsT_of_places K (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I L.trv L.htrv₁ tr htr hN
  intro v
  by_cases hv : v ∈ O.derivatives i
  · exact actLPerf_congr _ _ (by simp only [MovingOldDualityData.atA, dite_eq_left hv])
      (by simp only [MovingOldDualityData.atB, dite_eq_left hv]) (L.trv v) (L.htrv₁ v)
      (O.derivative_complement i p hK h2 hOther L v hv) (I.toLocal v)
  · exact actLPerf_congr _ _ (by simp only [MovingOldDualityData.atA, dite_eq_right hv])
      (by simp only [MovingOldDualityData.atB, dite_eq_right hv]) (L.trv v) (L.htrv₁ v)
      (O.old_complement i p hK h2 hOld L v) (I.toLocal v)

/-- Finite global duality on the enlarged support of stage `i` (tex 4385–4451).
Kind: PROVED. -/
theorem MovingOldDualityData.global_duality (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (I : O.Isotropy i)
    (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0)
    (h3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (globalDualityMap (O.pair i I) tr htr)) := by
  have : Finite (MinS (F.inclusion i) W i (F.α i)) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (F.α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (F.α i))) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (charInv (F.α i))))
  exact p.globalDuality (F.support i) 2 (Acoef i)
    (nekovarFiniteSetting_acoef K hK (F.support i) ((F.oldFinite i).insert (F.q i))
      (fun v hv => F.inclusion i (h2 v hv)) i)
    (MinS (F.inclusion i) W i (F.α i)) (MinS (F.inclusion i) W i (charInv (F.α i)))
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (weilPairingM_bijective W (O.roots i) (Acoef i) (F.α i) (O.full i))
    (weilPairingM_flip_bijective W (O.roots i) (Acoef i) (F.α i) (O.full i))
    (cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I tr htr h3

/-- The statement of the original trace and both original dualities at a moving stage (as
`OldDualityData.exists_original_trace_duality`, with the finite old support and the 2-adic
places of stage `i`; tex 4385–4451, 5055–5071). Kind: definition. -/
def MovingOldDualityData.ExistsOriginalTraceDuality : Prop :=
  ∀ (_p : ArithmeticPrints K) (_hK : IsTotallyComplex K)
    (_h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i)
    (_hOld : O.OtherOldComplements i) (_hOther : O.OtherDerivativeComplements i)
    (I : O.Isotropy i),
    ∃ (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
      (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap (O.pair i I) tr htr)) ∧
      QuasiIso (GHom.toCC (localDualityMap (O.pair i I) tr htr))

/-- **The original trace and both original dualities at a moving stage** (tex 4385–4451,
5055–5071). Kind: PROVED. -/
theorem MovingOldDualityData.exists_original_trace_duality :
    O.ExistsOriginalTraceDuality i := by
  intro p hK h2 hOld hOther I
  let S := F.support i
  have hS : S.Finite := (F.oldFinite i).insert (F.q i)
  let : Fintype (Places K S) := hS.fintype
  have h2S : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => F.inclusion i (h2 v hv)
  have hset := nekovarFiniteSetting_acoef K hK S hS h2S i
  have hT := cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i)
  have : Finite (MinS (F.inclusion i) W i (F.α i)) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (F.α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (F.α i))) :=
    inferInstanceAs (Finite (Mcoef K (F.oldSupport i) W i (charInv (F.α i))))
  obtain ⟨L, hL⟩ := p.traces S 2 (Acoef i) hset
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) hT
  obtain ⟨tr, htr, h3, hN⟩ := hL (MinS (F.inclusion i) W i (F.α i))
    (MinS (F.inclusion i) W i (charInv (F.α i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (F.α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I
  exact ⟨tr, htr, O.global_duality i p hK h2 I tr htr h3,
    O.local_complements i p hK h2 hOld hOther I L tr htr hN⟩

end OldDuality

section Stages

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]

/-- **The split-stage record on moving supports** (as `SplitStage`; tex 4385–4451,
4859–4873): the split projection, the self-paired split Selmer datum, its trace and the
global-duality quasi-isomorphism. Kind: definition. -/
structure MovingSplitStage (F : MovingStageFamily W) (i : ℕ)
    (Uq : GCx (Acoef i)) (ιq : GHom Uq (F.localCx i)) where
  /-- The split projection. -/
  projection : GHom (F.localCx i) (splitLocalComplex (Acoef i))
  /-- The self-paired split Selmer datum. -/
  pairing : SelPairData
    (splitSelData (F.globalCx i) (F.stageRes i projection) Uq (ghomComp ιq projection))
    (splitSelData (F.globalCx i) (F.stageRes i projection) Uq (ghomComp ιq projection))
  /-- The trace. -/
  trace : (coneCx pairing.resE).X 3 →ₗ[Acoef i] Acoef i
  /-- The trace kills coboundaries. -/
  trace_kills : ∀ z, trace ((coneCx pairing.resE).d 2 3 rfl z) = 0
  /-- The split global duality. -/
  duality : QuasiIso (GHom.toCC (globalDualityMap pairing trace trace_kills))

variable (F : MovingStageFamily W) (O : MovingOldDualityData F) (i : ℕ) [NeZero i]

/-- **The arithmetic input of a positive moving stage** (as `StageArithmeticInput`;
tex 4385–4451, 4809–4830, 4859–4873, 5035–5071). Kind: definition (GLUE and ELLIOT). -/
structure MovingStageArithmeticInput where
  /-- The original same-condition old paired diagram. -/
  oldPair : SelPairData (F.datum i) (F.datum i)
  /-- The original retained scalar local complex. -/
  scalarLocal : GCx (Acoef i)
  /-- The retained same-condition complex. -/
  retainedCondition : GCx (Acoef i)
  /-- Restriction in the scalar cup target. -/
  scalarRestriction : GHom oldPair.E scalarLocal
  /-- The retained condition inclusion. -/
  condition : GHom retainedCondition (F.localCx i)
  /-- The retained local cup. -/
  localCup : GPair (F.localCx i) (F.localCx i) scalarLocal
  /-- Localization compatibility and same-condition isotropy. -/
  retained : RetainedPlaceInput (F.datum i) oldPair (F.localCx i)
    scalarLocal retainedCondition (F.restriction i) scalarRestriction condition localCup
  /-- Original truncated isotropy. -/
  originalIsotropy : O.Isotropy i
  /-- The other old complements. -/
  otherOld : O.OtherOldComplements i
  /-- The other old derivative complements. -/
  otherDerivatives : O.OtherDerivativeComplements i
  /-- The original diagram comparison. -/
  originalComparison : OriginalDiagramComparison
    (allPlacePair (F.datum i) oldPair (F.localCx i) scalarLocal retainedCondition
      (F.restriction i) scalarRestriction condition localCup retained)
    (O.pair i originalIsotropy)
  /-- Trivial action on the localized module at the new prime. -/
  trivialAction : ∀ (g : Gloc K (F.q i))
    (m : ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i)), g • m = m
  /-- Fixed local roots of unity at the new prime. -/
  fixedRoots : ∀ (g : Gal(AlgebraicClosure ((F.q i).adicCompletion K)/
      (F.q i).adicCompletion K)) (ζ : AlgebraicClosure ((F.q i).adicCompletion K)),
    ζ ^ (2 ^ i) = 1 → g ζ = ζ
  /-- Local residual dimensions at the new prime. -/
  localDimensions : ∀ n : ℤ, Module.finrank (ResidueField (Acoef i))
    (residualCohomologyAt (F.localCx i) n) = splitLocalRank n

variable {F O i}

/-- The original compact trace of the retained local cup on the included split cochains (as
`originalCupTrace`; tex 4385–4388, 4438–4442). Kind: definition. -/
def movingOriginalCupTrace (S : MovingStageArithmeticInput F O i)
    (trN : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i)
    (Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)))
    (a b : ℤ) (hab : a + b = 2)
    (u : (splitLocalComplex (Acoef i)).X a) (v : (splitLocalComplex (Acoef i)).X b) :
    Acoef i :=
  let trAll : (coneCx (allTargetRes (F.datum i) S.oldPair S.scalarLocal
      S.scalarRestriction)).X 3 →ₗ[Acoef i] Acoef i :=
    pullScalarTrace (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
      S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup
      S.retained) (O.pair i S.originalIsotropy) S.originalComparison.scalar trN
  trAll (0, 0, S.localCup.P a b 2 hab (Rt.i.f a a rfl u) (Rt.i.f b b rfl v))

/-- **The linked split stage on moving supports** (as `LinkedSplitStage`, without the three
specialized trace identities; tex 4385–4451, 4859–4873). Kind: definition. -/
structure MovingLinkedSplitStage (S : MovingStageArithmeticInput F O i) where
  /-- The split stage. -/
  toSplitStage : MovingSplitStage F i S.retainedCondition S.condition
  /-- The normalized local retraction. -/
  localRetract : GRetract (F.localCx i) (splitLocalComplex (Acoef i))
  /-- The projection is the retraction's. -/
  projection_retract : localRetract.p = toSplitStage.projection
  /-- The projection homotopy link. -/
  projection_model : ∃ e : HomotopyEquiv (F.localCx i).toCC
    (splitLocalComplex (Acoef i)).toCC, e.hom = GHom.toCC toSplitStage.projection
  /-- The original compact trace. -/
  originalTrace : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i
  /-- It kills compact coboundaries. -/
  originalTrace_kills : ∀ z,
    originalTrace ((coneCx (O.pair i S.originalIsotropy).resE).d 2 3 rfl z) = 0
  /-- Original global duality. -/
  originalGlobalDuality : QuasiIso (GHom.toCC
    (globalDualityMap (O.pair i S.originalIsotropy) originalTrace originalTrace_kills))
  /-- Original local duality. -/
  originalLocalDuality : QuasiIso (GHom.toCC
    (localDualityMap (O.pair i S.originalIsotropy) originalTrace originalTrace_kills))
  /-- Local-cup trace transport. -/
  trace_transport : ∀ (a b : ℤ) (hab : a + b = 2)
    (u : (splitLocalComplex (Acoef i)).X a) (v : (splitLocalComplex (Acoef i)).X b),
    toSplitStage.trace (0, toSplitStage.pairing.cupL.P a b 2 hab u v) =
      movingOriginalCupTrace S originalTrace localRetract a b hab u v

/-- Local residual cohomology at the new prime is finite (tex 4392–4394, 4859–4868).
Kind: PROVED. -/
theorem movingLocalResidualFinite (F : MovingStageFamily W) (hloc : MilneLocalFiniteness)
    (i : ℕ) [NeZero i] (n : ℤ) :
    Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (F.localCx i) n) :=
  finite_residualCohomologyAt_of
    (localCx_residualCohomologyFinite K (F.support i) (F.coefficient i) hloc
      ⟨F.q i, Or.inl rfl⟩) n

/-- The statement of the linked split stage of a positive moving stage (as
`StageArithmeticInput.exists_linked_split`, with the 2-adic places of stage `i`).
Kind: definition. -/
def MovingStageArithmeticInput.ExistsLinkedSplit (S : MovingStageArithmeticInput F O i) :
    Prop :=
  ∀ (_p : ArithmeticPrints K) (_hK : IsTotallyComplex K)
    (_h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i),
    Nonempty (MovingLinkedSplitStage S)

/-- **The linked split stage of a positive moving stage** (tex 4385–4451, 4859–4873,
5035–5071): the original trace and dualities from the printed arithmetic results, transported
through the original comparison, and the normalized retraction at the new prime.
Kind: PROVED. -/
theorem MovingStageArithmeticInput.exists_linked_split (S : MovingStageArithmeticInput F O i) :
    S.ExistsLinkedSplit := by
  intro p hK h2
  obtain ⟨trN, htrN, hGN, hLN⟩ := O.exists_original_trace_duality i p hK h2
    S.otherOld S.otherDerivatives S.originalIsotropy
  let Qall := allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
    S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained
  let N := O.pair i S.originalIsotropy
  let trAll := pullScalarTrace Qall N S.originalComparison.scalar trN
  let htrAll := pullScalarTrace_kills Qall N S.originalComparison.scalar trN htrN
  have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
  obtain ⟨hG, hL⟩ := OriginalDiagramComparison.duality Qall N S.originalComparison
    trN htrN hGN hLN
  obtain ⟨Rt, Q, tr, htr, hdual, he, htrace⟩ := exists_stagePairing_trace_links W i
    (F.character i) (F.q i) (F.datum i) S.oldPair S.scalarLocal S.retainedCondition
    (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained trAll htrAll
    (F.odd i) (F.fullTorsion O.full i) S.trivialAction S.fixedRoots
    (movingLocalResidualFinite F p.localFinite i) S.localDimensions hG hL
  exact ⟨⟨⟨Rt.p, Q, tr, htr, hdual⟩, Rt, rfl, he, trN, htrN, hGN, hLN, htrace⟩⟩

end Stages

section Inputs

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]
  {F : MovingStageFamily W} {O : MovingOldDualityData F}

/-- **The residual package on moving supports**, with its bound: finite residual cohomology of
the moving stage complexes, the range `[0, 3]` and the uniform bound `B` (tex 4401–4406).
Kind: definition (ELLIOT input). -/
def MovingResidualPackage (F : MovingStageFamily W) (B : ℕ) : Prop :=
  (∀ i [NeZero i], ResidualCohomologyFinite (F.globalCx i)) ∧
    (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (F.globalCx i) n) = 0) ∧
    (∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (F.globalCx i) n) ≤ B)

/-- **The arithmetic inputs on moving supports** (as `ArithmeticInputs`, with the residual
package in place of the residual-support record; tex 4391–4451). Kind: definition (inputs). -/
structure MovingArithmeticInputs (F : MovingStageFamily W) (O : MovingOldDualityData F) where
  /-- The remaining old-condition term flatness. -/
  oldFlat : F.NontrivialOldFlat
  /-- The uniform residual bound. -/
  bound : ℕ
  /-- The residual package. -/
  residual : MovingResidualPackage F bound
  /-- The positive-stage arithmetic inputs. -/
  stage : ∀ i [NeZero i], MovingStageArithmeticInput F O i

/-- The retained conditions, zero at stage zero (tex 4391–4406, 4859–4873). Kind: definition. -/
def movingRetainedConditions (a : MovingArithmeticInputs F O) : ∀ i, GCx (Acoef i)
  | 0 => ZInQ.Manuscript.RC.SelmerComplex.zeroCx (Acoef 0)
  | i + 1 => (a.stage (i + 1)).retainedCondition

/-- The retained condition maps, zero at stage zero (tex 4391–4406, 4859–4873).
Kind: definition. -/
def movingRetainedInclusions (a : MovingArithmeticInputs F O) :
    ∀ i, GHom (movingRetainedConditions a i) (F.localCx i)
  | 0 => zeroGHom _ _
  | i + 1 => (a.stage (i + 1)).condition

/-- The zero coefficient stage needs no arithmetic input (tex 4391–4406). Kind: definition. -/
def movingZeroSplitStage (F : MovingStageFamily W) (Uq : GCx (Acoef 0))
    (ιq : GHom Uq (F.localCx 0)) : MovingSplitStage F 0 Uq ιq where
  projection := zeroGHom _ _
  pairing := zeroTargetPair (splitSelData (F.globalCx 0)
    (F.stageRes 0 (zeroGHom _ _)) Uq (ghomComp ιq (zeroGHom _ _)))
  trace := 0
  trace_kills _ := rfl
  duality := by
    have : Subsingleton (Acoef 0) := stageA_zero_subsingleton
    exact quasiIso_over_zeroRing _

/-- **The produced moving split stages** (as `producedStages'`): the zero stage, and at each
positive stage the split stage of a chosen linked split stage (tex 4385–4451, 4859–4873).
Kind: definition. -/
def producedStagesMoving' (a : MovingArithmeticInputs F O) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i) :
    ∀ i, MovingSplitStage F i (movingRetainedConditions a i) (movingRetainedInclusions a i)
  | 0 => movingZeroSplitStage F _ _
  | i + 1 =>
    (Classical.choice ((a.stage (i + 1)).exists_linked_split p hK (h2 (i + 1)))).toSplitStage

/-- Every positive produced projection is the forward map of a homotopy equivalence
(tex 4423–4437, 4859–4873). Kind: PROVED. -/
theorem producedStagesMoving'_projection_model (a : MovingArithmeticInputs F O)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K)
    (h2 : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ F.oldSupport i) :
    ∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC (splitLocalComplex (Acoef i)).toCC,
      e.hom = GHom.toCC (producedStagesMoving' a p hK h2 i).projection := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi.out
  exact (Classical.choice
    ((a.stage (j + 1)).exists_linked_split p hK (h2 (j + 1)))).projection_model

end Inputs

end MovingProducers

section MovingAssembly

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Linked moving inputs from the arithmetic inputs on moving supports** (as
`exists_linked_of_support_change`, with the residual package an input; tex 4385–4451,
4859–4873, 4976–5135): the produced moving split stages, their projection links and
`exists_linked_moving` give retained data `C`, `D` such that every retained local arithmetic on
them with its zero/two realization and `J = ρ_T(τ)`, together with the detection and the
side-to-stage isomorphisms, gives linked moving inputs. Kind: PROVED. -/
theorem exists_linked_of_moving_inputs (Z₀ Z₁ : TwoTermStage ι) {Fam : MovingStageFamily W}
    {O : MovingOldDualityData Fam} (a : MovingArithmeticInputs Fam O)
    (p : ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.ArithmeticPrints K)
    (hK : IsTotallyComplex K)
    (h2 : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ Fam.oldSupport i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C),
      ∀ rla : RetainedLocalArithmetic U C D, RetainedZeroTwo rla →
        rla.JAt P = conjMatrix Cn W hW P →
        finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
          (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U →
        ((selCx (finiteLimitSide (fibreLimitGlobal U hU P C)
          (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀) →
        ((selCx (singularLimitSide (fibreLimitGlobal U hU P C)
          (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) →
        Nonempty (ILStageStepMovingLinked P Cn W hW Z₀ Z₁) := by
  let s := producedStagesMoving' a p hK h2
  exact exists_linked_moving P Cn W hW Z₀ Z₁ Fam O.full a.oldFlat a.residual.1 a.bound
    a.residual.2.1 a.residual.2.2 (movingRetainedConditions a) (movingRetainedInclusions a)
    (fun i => (s i).projection) (fun i => (s i).pairing) (fun i => (s i).trace)
    (fun i => (s i).trace_kills) (fun i => (s i).duality) U hU
    (projection_model_of_homotopyEquiv (fun i => (s i).projection) U
      (producedStagesMoving'_projection_model a p hK h2))

end MovingAssembly

/-! **The fixed support is the constant case** -/

section Embedding

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {α : ∀ i, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)]

/-- **The fixed-support family as a moving family**: the RC53 group's `ActualStageFamily S₀ W α`
with the constant old support `S₀`. Kind: definition. -/
def MovingStageFamily.ofActual (hS₀ : S₀.Finite) (F : ActualStageFamily S₀ W α) :
    MovingStageFamily W where
  oldSupport _ := S₀
  oldFinite _ := hS₀
  α := α
  q := F.q
  new := F.new
  odd := F.odd
  old := F.old

omit [W.IsElliptic] in
/-- The stage datum of the constant family is the fixed-support one. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_datum (hS₀ : S₀.Finite) (F : ActualStageFamily S₀ W α)
    (i : ℕ) : (MovingStageFamily.ofActual hS₀ F).datum i = F.datum i := rfl

omit [W.IsElliptic] in
/-- The stage complex of the constant family is the fixed-support one. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_globalCx (hS₀ : S₀.Finite) (F : ActualStageFamily S₀ W α)
    (i : ℕ) : (MovingStageFamily.ofActual hS₀ F).globalCx i = F.globalCx i := rfl

omit [W.IsElliptic] in
/-- The local complex of the constant family is the fixed-support one. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_localCx (hS₀ : S₀.Finite) (F : ActualStageFamily S₀ W α)
    (i : ℕ) : (MovingStageFamily.ofActual hS₀ F).localCx i = F.localCx i := rfl

omit [W.IsElliptic] in
/-- The restriction of the constant family is the fixed-support one. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_restriction (hS₀ : S₀.Finite)
    (F : ActualStageFamily S₀ W α) (i : ℕ) :
    (MovingStageFamily.ofActual hS₀ F).restriction i = F.restriction i := rfl

omit [W.IsElliptic] in
/-- The localization of the constant family is the RC53 group's `stageRes`. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_stageRes (hS₀ : S₀.Finite) (F : ActualStageFamily S₀ W α)
    (i : ℕ) (p : GHom (F.localCx i) (splitLocalComplex (Acoef i))) :
    (MovingStageFamily.ofActual hS₀ F).stageRes i p =
      ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.stageRes F i p := rfl

omit [W.IsElliptic] in
/-- Full two-power torsion over `S₀` gives full torsion over every stage of the constant family.
Kind: PROVED. -/
theorem MovingStageFamily.ofActual_fullTorsionAt [HasFullTwoTorsion K S₀ W] (hS₀ : S₀.Finite)
    (F : ActualStageFamily S₀ W α) : (MovingStageFamily.ofActual hS₀ F).FullTorsionAt :=
  fun i => (HasFullTwoTorsion.full i : FullTorsion K S₀ W (2 ^ i))

omit [W.IsElliptic] in
/-- The flatness input of the constant family is the fixed-support one. Kind: PROVED. -/
theorem MovingStageFamily.ofActual_nontrivialOldFlat (hS₀ : S₀.Finite)
    (F : ActualStageFamily S₀ W α) :
    (MovingStageFamily.ofActual hS₀ F).NontrivialOldFlat ↔ F.NontrivialOldFlat := Iff.rfl

end Embedding

section EmbeddingProducers

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {α : ∀ i, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)] [HasFullTwoTorsion K S₀ W]

/-- The fixed-support old duality data as moving old duality data of the constant family.
Kind: definition. -/
def MovingOldDualityData.ofActual (hS₀ : S₀.Finite) {F : ActualStageFamily S₀ W α}
    (O : OldDualityData F) : MovingOldDualityData (MovingStageFamily.ofActual hS₀ F) where
  full := MovingStageFamily.ofActual_fullTorsionAt hS₀ F
  root _ := O.root
  parameter := O.parameter
  square _ := O.square
  nonzero _ := O.nonzero
  kummerPlaces _ := O.kummerPlaces
  locallyQuadratic i _ := O.locallyQuadratic i
  roots i _ := O.roots i
  derivatives := O.derivatives
  derivative_old := O.derivative_old
  derivativeA := O.derivativeA
  derivativeB := O.derivativeB
  originalOldA := O.originalOldA
  originalOldB := O.originalOldB

/-- The fixed-support stage input as a moving stage input of the constant family.
Kind: definition. -/
def MovingStageArithmeticInput.ofActual (hS₀ : S₀.Finite) {F : ActualStageFamily S₀ W α}
    {O : OldDualityData F} {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i) :
    MovingStageArithmeticInput (MovingStageFamily.ofActual hS₀ F)
      (MovingOldDualityData.ofActual hS₀ O) i where
  oldPair := S.oldPair
  scalarLocal := S.scalarLocal
  retainedCondition := S.retainedCondition
  scalarRestriction := S.scalarRestriction
  condition := S.condition
  localCup := S.localCup
  retained := S.retained
  originalIsotropy := S.originalIsotropy
  otherOld := S.otherOld
  otherDerivatives := S.otherDerivatives
  originalComparison := S.originalComparison
  trivialAction := S.trivialAction
  fixedRoots := S.fixedRoots
  localDimensions := S.localDimensions

end EmbeddingProducers

section EmbeddingStep

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The inputs on the fixed-support family as inputs on a moving family**: the family
`ofActual`, full torsion from `HasFullTwoTorsion K S W`, and the split-stage records unpacked
into projection, pairing, trace and duality. Kind: definition. -/
def ILStageStepFamily.toMoving {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamily P Cn W hW Z₀ Z₁) : ILStageStepMoving P Cn W hW Z₀ Z₁ where
  Fam := MovingStageFamily.ofActual X.hS X.Fam
  hFull := MovingStageFamily.ofActual_fullTorsionAt X.hS X.Fam
  hOld := X.hOld
  hres := X.hres
  B := X.B
  hbdd := X.hbdd
  hB := X.hB
  Uq := X.Uq
  ιq := X.ιq
  p i := (X.stages i).projection
  Q i := (X.stages i).pairing
  tr i := (X.stages i).trace
  htr i := (X.stages i).trace_kills
  hdual i := (X.stages i).duality
  U := X.U
  hU := X.hU
  C := X.C
  D := X.D
  E := X.E
  hlift := X.hlift
  hrank := X.hrank
  hrankB := X.hrankB
  rla := X.rla
  h02 := X.h02
  hJ := X.hJ
  hdet := X.hdet
  φ := X.φ
  φ' := X.φ'

/-- The stage complexes of `toMoving` are those of the fixed-support family. Kind: PROVED. -/
theorem ILStageStepFamily.toMoving_globalCx {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamily P Cn W hW Z₀ Z₁) (i : ℕ) :
    X.toMoving.Fam.globalCx i = X.Fam.globalCx i := rfl

/-- **The fixed support is the special case**: the switch of `toMoving` is the switch of the
fixed-support inputs. Kind: PROVED. -/
theorem ILStageStepFamily.toMoving_toILStageStep {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamily P Cn W hW Z₀ Z₁) :
    X.toMoving.toILStageStep = X.toILStageStep := rfl

/-- The linked inputs on the fixed-support family as linked inputs on a moving family.
Kind: definition. -/
def ILStageStepFamilyLinked.toMovingLinked {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamilyLinked P Cn W hW Z₀ Z₁) : ILStageStepMovingLinked P Cn W hW Z₀ Z₁ where
  toILStageStepMoving := X.toILStageStepFamily.toMoving
  projection_model := X.projection_model
  realized := X.realized

/-- The step data of `toMovingLinked` are those of the fixed-support inputs. Kind: PROVED. -/
theorem ILStageStepFamilyLinked.toMovingLinked_stepData {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepFamilyLinked P Cn W hW Z₀ Z₁) :
    X.toMovingLinked.stepData = X.stepData := rfl

end EmbeddingStep

/-! **The switching inputs on moving families** -/

section Switch

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Inner-limit switching inputs on moving families** (tex 2727–2741, 4255–4280, 4385–4451,
4976–5195, 5027–5086): as `InnerLimitSwitchFamily`, with each switch a linked switch on a moving
stage family (`ILStageStepMovingLinked`) whose limit sides' Selmer complexes are homotopy
equivalent to the fibres of the configuration and of its successor. Kind: definition (inputs). -/
structure InnerLimitSwitchMoving (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The linked moving switches, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepMovingLinked P Cn W hW (stage c) (stage (Φ.next c p)),
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {P Cn W hW} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **The inner-limit inputs of the moving inputs** (each step through its step data).
Kind: PROVED. -/
def InnerLimitSwitchMoving.toInner (X : InnerLimitSwitchMoving P Cn W hW Φ ι u) :
    InnerLimitSwitchModel P Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.stepData, hF, hS⟩

/-- **Regularity from the moving inputs at a height-one prime**. Kind: PROVED (from the
inputs). -/
theorem regular_of_innerLimitSwitchMoving (hP : P.height = 1) (hι : Function.Injective ι)
    (X : InnerLimitSwitchMoving P Cn W hW Φ ι u) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchModel hP hι X.toInner

/-- **The switching inputs on the fixed-support family as moving inputs** (each linked switch
through `toMovingLinked`, with the same side models). Kind: PROVED. -/
def InnerLimitSwitchFamily.toMoving (X : InnerLimitSwitchFamily P Cn W hW Φ ι u) :
    InnerLimitSwitchMoving P Cn W hW Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.toMovingLinked, hF, hS⟩

end Switch

end ZInQ.Manuscript.RC.Wiring
