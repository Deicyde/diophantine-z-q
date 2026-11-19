import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageFamily
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.StageLinks

/-!
# Theorem 5.3, Lane RC0 round 16: the linked switch inputs from the stage-link exports

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5195), with the switch
at a derivative label on the stage family of the text (tex 4385–4451, 4834–4907, 5027–5086,
5056–5062).

The RC53 group's linked assembly (`assemble_from_support_change_realized'`) chooses each positive
split stage together with its normalized local retraction and its original compact trace. The
assembled limit then carries, on the same retained diagram, the realization on the stage complexes
(`AssembledLimit.Realized`) and the stage links (`AssembledLimit.StageLinks`): the projection is
the forward map of a homotopy equivalence of the local cochains with the split model, and the
local-cup traces are the original ones (`OriginalStageTraceLinks`).

* `ILStageStepFamilyLinked.ofLinkedAssembly`: the linked switch inputs from such an assembled limit;
  the projection link comes from the stage links. Kind: PROVED.
* `exists_linked_of_support_change'`: from the RC53 group's arithmetic inputs and PRINTs, an
  assembled limit on which the linked switch inputs need only the retained local arithmetic
  (`rla`, `h02`, `hJ`), the detection and the side-to-stage isomorphisms. Kind: PROVED.
* `residueArithmeticOf`, `residueZeroTwoOf`: the retained local
  arithmetic and its zero/two realization on such a limit, from positive-stage arithmetic data
  `Y`, the scalar and conjugation lifts, and the three residue trace links. Kind: PROVED.
* `exists_linked_of_residue_identification`: with, in addition, the RC53 group's original residue
  trace identification (`OriginalResidueTraceIdentification`, the single remaining cochain
  identification, open) and the conjugation matrix at the fibre, an assembled limit on which the
  linked switch inputs need only the detection and the side-to-stage isomorphisms. Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.FibreDuality (conjMatrix)
open ZInQ.Manuscript.RC.Limits (StageA stageMap stageIdeal)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex fibreLimitGlobal limitRelaxed
  finiteLimitSide singularLimitSide Vec2)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS NekovarProp788ii)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (ActualStageFamily
  ArithmeticInputs AssembledLimit OldDualityData StandardOldReference ArithmeticPrints
  ResidualSupportControl ActualSupportPresentation StageArithmeticInput stageRes
  retainedConditions retainedInclusions OriginalResidueTraceIdentification
  assemble_from_support_change_realized' assemble_from_support_change_residue_realized')
open ZInQ.Contrib.RC53Assist.ResidueIdentity (RetainedLocalArithmetic RetainedZeroTwo
  StageArithmeticData)

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  {α : ∀ i, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  {Fam : ActualStageFamily S W α} {O : OldDualityData Fam} {R : StandardOldReference S W α}

/-- The finite coefficient stages carry their discrete topology (the topology of the stage
arithmetic data, tex 2723–2727). -/
local instance residueStage_topology (i : ℕ) : TopologicalSpace (StageA i) := ⊥

/-- The stage topology is discrete. -/
local instance residueStage_discrete (i : ℕ) : DiscreteTopology (StageA i) := ⟨rfl⟩

/-- The two-power exponent of the stage arithmetic data is nonzero. -/
local instance residueExponent_neZero (i : ℕ) : NeZero (2 ^ i) :=
  ⟨pow_ne_zero i two_ne_zero⟩

/-! **The linked inputs from the linked assembly** -/

section LinkedAssembly

variable {width : ℕ} {a : ArithmeticInputs Fam O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ cofinite}

/-- **The linked switch inputs from an assembled limit with its stage links**: as
`ILStageStepFamilyLinked.ofAssembled`, with the projection link read from the stage links (the
projection is the forward map of a homotopy equivalence at every positive stage). Kind: PROVED. -/
def ILStageStepFamilyLinked.ofLinkedAssembly {Z₀ Z₁ : TwoTermStage ι} (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : AssembledLimit a U hU Cn hW) (hL : L.Realized) (hlinks : L.StageLinks)
    (rla : RetainedLocalArithmetic U L.C L.D) (h02 : RetainedZeroTwo rla)
    (hJ : rla.JAt P = conjMatrix Cn W hW P)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C)
      (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P L.C)
      (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) :
    ILStageStepFamilyLinked P Cn W hW Z₀ Z₁ :=
  ILStageStepFamilyLinked.ofAssembled p hK hS h2 L hL rla h02 hJ hdet φ φ'
    (projection_model_of_homotopyEquiv (fun i => (L.stages i).projection) U hlinks.1)

end LinkedAssembly

variable (P Cn W hW) in
/-- **The linked inputs from the RC53 group's arithmetic inputs, through the stage-link export**
(`assemble_from_support_change_realized'`): there is an assembled limit `L` (on the stages chosen
with their retractions and original traces) such that every retained local arithmetic on it with
its zero/two realization and `J = ρ_T(τ)`, together with the detection and the side-to-stage
isomorphisms, gives linked inputs. Kind: PROVED. -/
theorem exists_linked_of_support_change' (Z₀ Z₁ : TwoTermStage ι) (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Pr : ActualSupportPresentation Fam R) (oldFlat : Fam.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput Fam O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ∃ T : ResidualSupportControl Fam R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs Fam O R 6) U hU Cn hW,
        L.Realized ∧ L.StageLinks ∧
        ∀ (rla : RetainedLocalArithmetic U L.C L.D), RetainedZeroTwo rla →
          rla.JAt P = conjMatrix Cn W hW P →
          finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
            (limitRelaxed (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).U →
          ((selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀) →
          ((selCx (singularLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) →
          Nonempty (ILStageStepFamilyLinked P Cn W hW Z₀ Z₁) := by
  obtain ⟨T, L, -, hL, hlinks⟩ :=
    assemble_from_support_change_realized' p h788 hK hS h2 Pr oldFlat stage U hU Cn hW
  exact ⟨T, L, hL, hlinks, fun rla h02 hJ hdet φ φ' =>
    ⟨ILStageStepFamilyLinked.ofLinkedAssembly p hK hS h2 L hL hlinks rla h02 hJ hdet φ φ'⟩⟩

/-! **The retained local arithmetic from the residue trace links** -/

section Residue


variable {width : ℕ} {a : ArithmeticInputs Fam O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ cofinite}

/-- **The retained local arithmetic of an assembled limit** (the RC53 group's
`RetainedLocalArithmetic.of_splitStages` on the limit's own stages): from positive-stage
arithmetic data `Y`, the unit, tame-scale and conjugation lifts with their identifications and
the derivative congruence, and the one/one and two/zero residue trace links of the limit's stages
(`AssembledLimit.ResidueTraceLinks`). Kind: PROVED (a construction). -/
def residueArithmeticOf (L : AssembledLimit a U hU Cn hW)
    (Y : ∀ i, ∀ [NeZero i], StageArithmeticData i)
    (ε : ℕ → Lambdaˣ) (s : ℕ → Lambda) (J : Matrix (Fin 2) (Fin 2) Lambda)
    (hJ : J * J = 1) (hJdet : J.det = -1)
    (hε : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (Y i).ε)
    (hs : ∀ i, ∀ [NeZero i], stageMap i (s i) = (Y i).tameScale)
    (hmat : ∀ i, ∀ [NeZero i], (Y i).J = J.map (stageMap i))
    (hcongr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i)
    (htr : L.ResidueTraceLinks Y) : RetainedLocalArithmetic U L.C L.D :=
  RetainedLocalArithmetic.of_splitStages Y ε s J hJ hJdet hε hs hmat hcongr
    (fun i => Fam.globalCx i) (retainedConditions a)
    (fun i => stageRes Fam i (L.stages i).projection)
    (fun i => ghomComp (retainedInclusions a i) (L.stages i).projection)
    (fun i => (L.stages i).pairing) (fun i => (L.stages i).trace)
    L.local_lift htr.2.1 htr.2.2

/-- **The zero/two realization of that retained local arithmetic** (the RC53 group's
`RetainedZeroTwo.of_splitStages`, from the zero/two residue trace link). Kind: PROVED. -/
theorem residueZeroTwoOf (L : AssembledLimit a U hU Cn hW)
    (Y : ∀ i, ∀ [NeZero i], StageArithmeticData i)
    (ε : ℕ → Lambdaˣ) (s : ℕ → Lambda) (J : Matrix (Fin 2) (Fin 2) Lambda)
    (hJ : J * J = 1) (hJdet : J.det = -1)
    (hε : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (Y i).ε)
    (hs : ∀ i, ∀ [NeZero i], stageMap i (s i) = (Y i).tameScale)
    (hmat : ∀ i, ∀ [NeZero i], (Y i).J = J.map (stageMap i))
    (hcongr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i)
    (htr : L.ResidueTraceLinks Y) :
    RetainedZeroTwo (residueArithmeticOf L Y ε s J hJ hJdet hε hs hmat hcongr htr) :=
  RetainedZeroTwo.of_splitStages _
    (fun i => Fam.globalCx i) (retainedConditions a)
    (fun i => stageRes Fam i (L.stages i).projection)
    (fun i => ghomComp (retainedInclusions a i) (L.stages i).projection)
    (fun i => (L.stages i).pairing) (fun i => (L.stages i).trace)
    L.local_lift htr.1

/-- The conjugation matrix of that retained local arithmetic at a fibre is the lift `J` read at
the fibre. Kind: PROVED. -/
theorem residueArithmeticOf_JAt (L : AssembledLimit a U hU Cn hW)
    (Y : ∀ i, ∀ [NeZero i], StageArithmeticData i)
    (ε : ℕ → Lambdaˣ) (s : ℕ → Lambda) (J : Matrix (Fin 2) (Fin 2) Lambda)
    (hJ : J * J = 1) (hJdet : J.det = -1)
    (hε : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (Y i).ε)
    (hs : ∀ i, ∀ [NeZero i], stageMap i (s i) = (Y i).tameScale)
    (hmat : ∀ i, ∀ [NeZero i], (Y i).J = J.map (stageMap i))
    (hcongr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i)
    (htr : L.ResidueTraceLinks Y) :
    (residueArithmeticOf L Y ε s J hJ hJdet hε hs hmat hcongr htr).JAt P =
      J.map (algebraMap Lambda (ResAt P)) :=
  rfl

end Residue

variable (P Cn W hW) in
/-- **The linked inputs from the RC53 group's arithmetic inputs and the original residue trace
identification** (`assemble_from_support_change_residue_realized'`): given positive-stage
arithmetic data `Y`, the identification of the chosen stages' original compact local-cup traces
with `Y`'s transported cups (`OriginalResidueTraceIdentification`, the RC53 group's open item), the
scalar and conjugation lifts, and the conjugation lift read at the fibre equal to `ρ_T(τ)`, there
is an assembled limit `L` on which the detection and the side-to-stage isomorphisms give linked
inputs. The retained local arithmetic and its zero/two realization are constructed
(`residueArithmeticOf`, `residueZeroTwoOf`). Kind: PROVED. -/
theorem exists_linked_of_residue_identification (Z₀ Z₁ : TwoTermStage ι)
    (p : ArithmeticPrints K) (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K)
    (hS : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Pr : ActualSupportPresentation Fam R) (oldFlat : Fam.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput Fam O i)
    (Y : ∀ i, ∀ [NeZero i], StageArithmeticData i)
    (hid : ∀ i [NeZero i], OriginalResidueTraceIdentification (stage i)
      ((stage i).chosen_links p hK hS h2) (Y i))
    (ε : ℕ → Lambdaˣ) (s : ℕ → Lambda) (J : Matrix (Fin 2) (Fin 2) Lambda)
    (hJ : J * J = 1) (hJdet : J.det = -1)
    (hε : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (Y i).ε)
    (hs : ∀ i, ∀ [NeZero i], stageMap i (s i) = (Y i).tameScale)
    (hmat : ∀ i, ∀ [NeZero i], (Y i).J = J.map (stageMap i))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (hcongr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i)
    (hJP : J.map (algebraMap Lambda (ResAt P)) = conjMatrix Cn W hW P) :
    ∃ T : ResidualSupportControl Fam R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs Fam O R 6) U hU Cn hW,
        finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
            (limitRelaxed (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).U →
          ((selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀) →
          ((selCx (singularLimitSide (fibreLimitGlobal U hU P L.C)
            (L.D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁) →
          Nonempty (ILStageStepFamilyLinked P Cn W hW Z₀ Z₁) := by
  obtain ⟨T, L, -, hL, hlinks, htr⟩ := assemble_from_support_change_residue_realized'
    p h788 hK hS h2 Pr oldFlat stage Y hid U hU Cn hW
  refine ⟨T, L, fun hdet φ φ' => ⟨ILStageStepFamilyLinked.ofLinkedAssembly p hK hS h2 L hL
    hlinks (residueArithmeticOf L Y ε s J hJ hJdet hε hs hmat hcongr htr)
    (residueZeroTwoOf L Y ε s J hJ hJdet hε hs hmat hcongr htr) ?_ hdet φ φ'⟩⟩
  rw [residueArithmeticOf_JAt]
  exact hJP

end ZInQ.Manuscript.RC.Wiring
