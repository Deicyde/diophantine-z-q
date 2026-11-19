import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Pin
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Dual
import ZInQKernel.Contrib.CloudB3E2Norm.H20PairedLift

/-!
# The orthogonal side of the retention on the presentation with staged supports

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4175: the
paired strict-to-primitive map, the retained orthogonal conditions, the generic paired strict
lift `j z_S = e_q^c z_{P⊥}` with `e_q^c = e_q`, and `λ_R ∘ i = e_q λ_P`), the paired class
(tex 3736–3753) and the inner limit (tex 4385–4451), on lane RC32's `StagedPresentation`.

* **The paired side at the stage `s`** (definitions, PROVED): the paired character
  `alphaF' s s' = alphaStage s' … (ξ_s)⁻¹ (ψf s s')` (the construction at `π⁻¹`, as in lane E2's
  `hlift_actual`) with open kernel (`hπ'`, `alphaF'_isOpenKer`, `alphaShap'_isOpenKer`) and the
  module instances of `CommonCoordinate19Staged.lean`; the objects `famM'`, `famX'`, `famEU'`
  (`famEU'_i`) and the transported conditions `famCondsT` (lane E2's `stageCondsK` at `π⁻¹`,
  with `psiTrivialAt2N_inv`), injective in degree one and surjective in degree zero
  (`pairedConds_injective`, `pairedConds_surjective₀`, `pairedEU_surjective₀`). Lane E2 does not
  instantiate the old orthogonal conditions `Δ'` (a parameter of its `DualPres` and of
  `hlift_actual`); here they are the parameter `Δo` of the stage.
* **`DualStepS P s Δo Tm β hβ hβc i hp`** (definition, data): the inputs of the step `i` at the
  stage `s` on the orthogonal side: lane RC32's `DualCupInputs` (GLUE, owner lane U1), a trace of
  the pinned cone with `htr`, lane E2's `OrthComparisonInverse` (GLUE), and the transported
  classes with their norm identity at the leaf's point factor (`hnorm`, a hypothesis; from global
  classes by `DualStepS.ofGlobal`). **`DualStepS.R`**: the step's retention
  `StepRetention.ofDual …` with `e` the leaf's point factor (`DualStepS.R_e`, `R_tr`, `R_zS`,
  `R_zP`).
* **The transported global identity** (PROVED): `pairedNorm_of_global` (as lane E2's
  `gxClass_step_of_global`, for global classes of the paired module with local lifts: a global
  identity `g_R = e g_T + d b_G` gives the norm identity of the transported presentation) and
  **`DualStepS.ofGlobal`**; `leafFactor_paired` (lane E2's `pointFactor_paired` at the stage: the
  factor at `π⁻¹` is the leaf's factor at `π`).
* **Consecutive steps** (PROVED): **`DualStepS.consecutive`** (from `RetainedHomotopyStep`, one
  trace, one inverse and consecutive transported classes, `λ_P` of the step `i + 1` is `λ_R` of
  the step `i`) and **`DualStepS.hP_succ`**: on the staged chain, lane RC32's `hP` at the step
  `i + 1` follows from `hR` at the step `i`.

Kinds: definitions, PROVED; GLUE inputs `DualCupInputs`, `OrthComparisonInverse` and
`RetainedHomotopyStep`. For the text's old orthogonal conditions (Kummer above `2N`, zero
elsewhere) with the comparison identity at `Pk` and zero into the full conditions elsewhere, the
inverse `OrthComparisonInverse` is uninhabited at the finite stages once two places outside `Pk`
carry a nonzero invariant (lane E1's chain-level counterexample, the obstruction
`⊕_{v ∈ Z} H⁰(K_v, M)`); the text's inverse exists after the inner limit, over `𝒪[G]`, with the
retained lattice comparison at the old places (tex 3704–3790).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain TensorProduct
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef unitPowHom)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage alphaShap stageCondsK stageIsoA
  PsiTrivialAt2N univChar stageCondK_injective stageCondK_surjective₀ genuineιq_surjective₀
  psiTrivialAt2N_inv pointFactor_paired eK hnorm_changeIncl presι_injective exists_presLift₀)
open ZInQ.Contrib.CloudB3E2.DualPres (OrthComparisonInverse)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section PairedObjects

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

namespace StagedPresentation

/-- **The paired character at the precision `s'`** over `G_{K,S₀ s}`: `χ_{h_x} (1 + t)^{-ξ_s}`,
lane E2's `alphaStage` at `π⁻¹` (tex 3736–3753, 4166–4171). Kind: definition. -/
abbrev alphaF' (s s' : ℕ) : GKS C.K (P.S₀ s) →* (Acoef s')ˣ :=
  alphaStage s' (P.sh s) (P.hs s) (P.hs0 s) (P.ξ s)⁻¹ (P.ψf s s')

omit [(Ecurve ℓ).IsElliptic] in
/-- The inverse exponent has the kernel of the exponent (tex 2729). Kind: PROVED. -/
theorem ker_ξ_inv (s : ℕ) : ((P.ξ s)⁻¹).ker = (P.ξ s).ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]

omit [(Ecurve ℓ).IsElliptic] in
/-- The inverse exponent has open kernel over `G_{K,S₀ s}` (tex 2729). Kind: PROVED. -/
theorem hπ' (s : ℕ) : IsOpen (((P.ξ s)⁻¹).ker : Set (GKS C.K (P.S₀ s))) := by
  rw [P.ker_ξ_inv s]
  exact P.hπ s

/-- **The paired character has open kernel at every precision** (tex 2726–2729).
Kind: PROVED. -/
instance alphaF'_isOpenKer (s s' : ℕ) : IsOpenKer (P.alphaF' s s') :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _
    (isOpenKer_map (quadChar (P.sh s) (P.hs s) (P.hs0 s)) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (P.ξ s)⁻¹ (P.hπ' s) (P.ψf s s'))

/-- Lane E2's Shapiro-level paired character has open kernel (tex 2726–2729). Kind: PROVED. -/
instance alphaShap'_isOpenKer (s : ℕ) :
    IsOpenKer (alphaShap (P.sh s) (P.hs s) (P.hs0 s) (P.ξ s)⁻¹) :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _
    (isOpenKer_map (quadChar (P.sh s) (P.hs s) (P.hs0 s)) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (P.ξ s)⁻¹ (P.hπ' s) (univChar _))

/-- **The paired module over the stage ring** through `stageEquiv s'` (tex 2724–2727,
3736–3753). Kind: definition. -/
instance mcoefModule' (s s' : ℕ) :
    Module (StageRing s') (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) :=
  stageCompModule s' (P.alphaF' s s') _

/-- The Galois action on the paired module commutes with the stage ring (tex 2724–2727).
Kind: PROVED. -/
instance mcoefSMulComm' (s s' : ℕ) : SMulCommClass (GKS C.K (P.S₀ s)) (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) :=
  stageComp_smulCommClass s' (P.alphaF' s s') _

/-- The rank-two stage basis of the paired module (tex 2724–2727, 2836–2838).
Kind: definition. -/
def mcoefBasis' (s s' : ℕ) : Module.Basis (Fin 2) (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) :=
  Module.Basis.ofEquivFun ((stageCoefEquiv s' _ (P.alphaF' s s')).trans
    (stageBasis (tateBasis (K := C.K) (S := P.S₀ s) (W := (Ecurve ℓ).baseChange C.K)) s'))

/-- The paired module is free of rank two over the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefFree' (s s' : ℕ) : Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) :=
  Module.Free.of_basis (P.mcoefBasis' s s')

/-- The paired module is discrete for the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefContinuousConstSMul' (s s' : ℕ) : ContinuousConstSMul (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

end StagedPresentation

/-- **The paired coefficient modules of the stage `s`** (tex 3736–3753, 4160–4164): lane E2's
`MinS` at the paired character over `G_{K,S₀ s}`, inflated to `G_{K,S s}`. Kind: definition. -/
abbrev famM' (s : ℕ) : ℕ → Type := fun s' =>
  MinS (P.hS s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')

/-- The paired modules are free over the stage rings (tex 2724–2727). Kind: PROVED. -/
instance famM'_free (s s' : ℕ) : Module.Free (StageRing s') (famM' P s s') :=
  inferInstanceAs (Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')))

/-- The paired modules are finite (tex 2724–2727). Kind: PROVED. -/
instance famM'_finite (s s' : ℕ) : Finite (famM' P s s') :=
  inferInstanceAs (Finite (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')))

/-- **The unramified representations of the paired side** at the places of the chain
(tex 3470–3498, 4163–4164): lane E2's `urRep` at `place s j`. Kind: definition. -/
abbrev famX' (s s' : ℕ) :
    (j : P.ι × Bool) → TopRep.{0} (StageRing s') (GUr C.K (P.place s j).1) :=
  urChainRep (P.place s) (P.hwp s)
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s'))

/-- They are discrete modules (tex 3470–3498). Kind: PROVED. -/
instance famX'_continuousSMul (s s' : ℕ) (j : P.ι × Bool) :
    ContinuousSMul (GUr C.K (P.place s j).1) (famX' P s s' j).V :=
  urRep_continuousSMul (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s'))
    (newPlace (P.place s j) (P.hwp s j))

/-- They are free over the stage ring (tex 3470–3498). Kind: PROVED. -/
instance famX'_free (s s' : ℕ) (j : P.ι × Bool) :
    Module.Free (StageRing s') (famX' P s s' j).V :=
  inferInstanceAs (Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')))

/-- The splits of the genuine inflations of the paired side exist (tex 3470–3487;
`exists_genuineSplitsS`). Kind: PROVED. -/
theorem famEU'_exists (s s' : ℕ) :
    ∃ EU : ∀ j, SplitInclusion
        (genuineUq C.K (P.S s) (StageRing s') (P.place s j) (famX' P s s' j))
        (genuineLq C.K (P.S s) (StageRing s') (famM' P s s') (P.place s j)),
      ∀ j, (EU j).i = genuineιq C.K (P.S s) (StageRing s') (famM' P s s') (P.place s j)
        (famX' P s s' j)
        (urId (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s'))
          (newPlace (P.place s j) (P.hwp s j)))
        (urId_compat (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) (P.place s j)
          (P.hwp s j)) :=
  exists_genuineSplitsS C.K (P.S s) (StageRing s') (famM' P s s') (P.place s) (famX' P s s') _ _
    (fun j => (urId_bijective (StageRing s') _ (P.hS s) (newPlace (P.place s j) (P.hwp s j))).1)

/-- **The splits of the genuine inflations of the paired side** along `urId` (tex 3470–3487).
Kind: definition. -/
def famEU' (s s' : ℕ) (j : P.ι × Bool) :
    SplitInclusion (genuineUq C.K (P.S s) (StageRing s') (P.place s j) (famX' P s s' j))
      (genuineLq C.K (P.S s) (StageRing s') (famM' P s s') (P.place s j)) :=
  Classical.choose (famEU'_exists P s s') j

/-- Their inclusions are the genuine inflations along `urId` (tex 3470–3487). Kind: PROVED. -/
theorem famEU'_i (s s' : ℕ) (j : P.ι × Bool) :
    (famEU' P s s' j).i = genuineιq C.K (P.S s) (StageRing s') (famM' P s s') (P.place s j)
        (famX' P s s' j)
        (urId (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s'))
          (newPlace (P.place s j) (P.hwp s j)))
        (urId_compat (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF' s s')) (P.place s j)
          (P.hwp s j)) :=
  Classical.choose_spec (famEU'_exists P s s') j

/-- **The transported old conditions of the stage `s`** (tex 3740–3745, 2743–2760): lane E2's
`stageCondsK` at the paired character (Kummer at `Pk`, full at `S₀ s − Pk`), at the zero ring the
full conditions; the second conditions of lane E2's `OrthComparisonInverse`, as in
`hlift_actual`. Kind: definition. -/
def famCondsT (s : ℕ) : (s' : ℕ) → LocalConditions (StageRing s') (GKS C.K (P.S s))
    (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
    (famM' P s s')
  | 0 => relaxedConditions (StageRing 0) (GKS C.K (P.S s))
      (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
      (famM' P s 0)
  | s' + 1 =>
    letI := acoefTop (s' + 1)
    haveI := acoefTop_discrete (s' + 1)
    letI := stageIsoA (s' + 1)
    stageCondsK (P.hS s) ((Ecurve ℓ).baseChange C.K) (s' + 1) (P.sh s) (P.hs s) (P.hs0 s)
      (HasFullTwoTorsion.full (s' + 1)) (P.ξ s)⁻¹ (P.ψf s (s' + 1)) P.Pk
      (psiTrivialAt2N_inv (s' + 1) (P.ξ s) (P.ψf s (s' + 1)) (P.hΨ s (s' + 1)))
      (StageRing (s' + 1))

/-- The transported conditions are injective in degree one at a positive stage (lane E2's
`stageCondK_injective`; tex 2743–2760). Kind: PROVED. -/
theorem pairedConds_injective (t : ℕ) (v₀ : Places C.K (P.S₀ (t + 1))) :
    Function.Injective (((famCondsT P (t + 1) (t + 1)).i v₀).f 1 1 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_injective (P.hS (t + 1)) ((Ecurve ℓ).baseChange C.K) (t + 1) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.ξ (t + 1))⁻¹
    (P.ψf (t + 1) (t + 1)) P.Pk
    (psiTrivialAt2N_inv (t + 1) (P.ξ (t + 1)) (P.ψf (t + 1) (t + 1)) (P.hΨ (t + 1) (t + 1)))
    (StageRing (t + 1)) v₀

/-- The transported conditions are surjective in degree zero at a positive stage (lane E2's
`stageCondK_surjective₀`; tex 2743–2760). Kind: PROVED. -/
theorem pairedConds_surjective₀ (t : ℕ) (v₀ : Places C.K (P.S₀ (t + 1))) :
    Function.Surjective (((famCondsT P (t + 1) (t + 1)).i v₀).f 0 0 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_surjective₀ (P.hS (t + 1)) ((Ecurve ℓ).baseChange C.K) (t + 1)
    (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1))
    (P.ξ (t + 1))⁻¹ (P.ψf (t + 1) (t + 1)) P.Pk
    (psiTrivialAt2N_inv (t + 1) (P.ξ (t + 1)) (P.ψf (t + 1) (t + 1)) (P.hΨ (t + 1) (t + 1)))
    (StageRing (t + 1)) v₀

/-- The genuine inflations of the paired side are surjective in degree zero (lane E2's
`genuineιq_surjective₀`; tex 3470–3487). Kind: PROVED. -/
theorem pairedEU_surjective₀ (s : ℕ) (j : P.ι × Bool) :
    Function.Surjective ((famEU' P s s j).i.f 0 0 rfl) := by
  rw [famEU'_i P s s j]
  exact genuineιq_surjective₀ (P.place s j) _ _ _
    (urId_bijective (StageRing s) _ (P.hS s) (newPlace (P.place s j) (P.hwp s j))).2

end PairedObjects


section Step

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ) (s : ℕ)
  (Δo : LocalConditions (StageRing s) (GKS C.K (P.S s))
    (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
    (famM' P s s))
  (Tm : Type) [AddCommGroup Tm] [Module (StageRing s) Tm] [DistribMulAction (GKS C.K (P.S s)) Tm]
  [SMulCommClass (GKS C.K (P.S s)) (StageRing s) Tm] [TopologicalSpace Tm] [ContinuousAdd Tm]
  [ContinuousConstSMul (StageRing s) Tm] [ContinuousSMul (GKS C.K (P.S s)) Tm]
  (β : famM' P s s →ₗ[StageRing s] famM P s s →ₗ[StageRing s] Tm)
  (hβ : ∀ (g : GKS C.K (P.S s)) (a : famM' P s s) (b : famM P s s), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun y : famM' P s s × famM P s s => β y.1 y.2)

/-- **The leaf's point factor at the step `i` of the stage `s`** (tex 4158, 4169, 4171):
`pointFactor a_i z_i z_i⁻¹` with the leaf's trace and points at the stage. Kind: definition. -/
abbrev leafFactorS (i : ℕ) : StageRing s :=
  pointFactor (leafTrS P s i) (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i)
    (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i)

/-- **The inputs of the step `i` at the stage `s` on the orthogonal side** (tex 4157–4175,
3736–3753, 3829–3833): lane RC32's cup-product input (GLUE, owner lane U1), a trace of the pinned
cone vanishing on boundaries, lane E2's inverse of the orthogonal comparison (GLUE), and the
transported classes of the paired presentation with their norm identity at the leaf's point
factor (a hypothesis; `DualStepS.ofGlobal` derives it from a transported global identity).
Kind: definition (data). -/
structure DualStepS (i : ℕ) (hp : P.pidx i ∉ chainT P.pidx i) where
  /-- the cup-product input of the switch (GLUE, owner lane U1; tex 4162–4168) -/
  cup : DualCupInputs C.K (P.S₀ s) (P.S s) (StageRing s) (famM P s s) (famConds P s s)
    (P.place s) (famX P s s) (famEU P s s) (famM' P s s) Δo (famX' P s s) (famEU' P s s) Tm β hβ
    hβc (chainT P.pidx i) (P.pidx i) hp
  /-- the trace of the pinned cone (tex 3829–3833) -/
  tr : (coneCx (dualCupResE C.K (P.S₀ s) (P.S s) (StageRing s) (P.place s) Tm)).X 3 →ₗ[StageRing s]
    StageRing s
  /-- it vanishes on boundaries (tex 3829–3833) -/
  htr : ∀ y, tr ((coneCx (dualCupResE C.K (P.S₀ s) (P.S s) (StageRing s) (P.place s) Tm)).d 2 3
    rfl y) = 0
  /-- lane E2's inverse of the orthogonal comparison (GLUE; tex 3740–3745; at the finite stages
  with the text's old orthogonal conditions it is uninhabited, see the module docstring) -/
  orth : OrthComparisonInverse C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) Δo
    (famCondsT P s s) (P.place s) (famX' P s s) (famEU' P s s)
  /-- the transported relaxed class (tex 4169–4171) -/
  zR : (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
    (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).X 1
  /-- the transported primitive class (tex 4169–4171) -/
  zP : (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
    (famX' P s s) (famEU' P s s) (chainT P.pidx i)).X 1
  /-- the retained boundary (tex 4169–4171) -/
  b : (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
    (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).X 0
  /-- the transported norm identity at the leaf's point factor (tex 4169–4171) -/
  hnorm : zR = leafFactorS P s i • (suppInclS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s)
      (famCondsT P s s) (P.place s) (famX' P s s) (famEU' P s s) (chainT P.pidx i) (P.pidx i)).f
      1 1 rfl zP +
    (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
      (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).d 0 1 rfl b

variable {P s Δo Tm β hβ hβc}

/-- **The retention of the step from the orthogonal side** (tex 4157–4175, 4385–4451): lane
RC32's `StepRetention.ofDual` with the step's inputs and `e` the leaf's point factor; the value of
the field `R` of `StageChainsS` at the step. Kind: definition. -/
def DualStepS.R {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (Dd : DualStepS P s Δo Tm β hβ hβc i hp) :
    StepRetention C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
      (famEU P s) s (chainT P.pidx i) (P.pidx i) hp :=
  StepRetention.ofDual C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
    (famEU P s) hp Dd.cup Dd.tr Dd.htr Dd.orth Dd.zR Dd.zP (leafFactorS P s i) Dd.b Dd.hnorm

/-- The point factor of the retention is the leaf's (tex 4158, 4169). Kind: PROVED
(definitional). -/
theorem DualStepS.R_e {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (Dd : DualStepS P s Δo Tm β hβ hβc i hp) : Dd.R.e = leafFactorS P s i :=
  rfl

/-- The trace of the retention is the step's (tex 3829–3833). Kind: PROVED (definitional). -/
theorem DualStepS.R_tr {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (Dd : DualStepS P s Δo Tm β hβ hβc i hp) : Dd.R.tr = Dd.tr :=
  rfl

/-- The strict class of the retention is `ψ_{T ∪ {p}}(z'_R)` (tex 4169–4171). Kind: PROVED
(definitional). -/
theorem DualStepS.R_zS {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (Dd : DualStepS P s Δo Tm β hβ hβc i hp) :
    Dd.R.zS = dualZS Dd.orth (chainT P.pidx i) (P.pidx i) Dd.zR :=
  rfl

/-- The orthogonal class of the retention is `ψ_T(z'_P)` (tex 4169–4171). Kind: PROVED
(definitional). -/
theorem DualStepS.R_zP {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (Dd : DualStepS P s Δo Tm β hβ hβc i hp) : Dd.R.zP = dualZP Dd.orth (chainT P.pidx i) Dd.zP :=
  rfl

/-- **Consecutive steps on the orthogonal side** (tex 4159, 4164–4174, 3750–3752): for the step
`i` and the step `i + 1` at the stage `s`, with compatible retained homotopies
(`RetainedHomotopyStep`), one trace, one inverse `Ψ`, and the transported primitive class of the
step `i + 1` equal to the transported relaxed class of the step `i`, the primitive paired
functional of the step `i + 1` is the relaxed paired functional of the step `i`
(`StepRetention.ofDual_consecutive`). Kind: PROVED. -/
theorem DualStepS.consecutive {i : ℕ} {hp₁ : P.pidx i ∉ chainT P.pidx i}
    {hp₂ : P.pidx (i + 1) ∉ chainT P.pidx (i + 1)}
    (D₁ : DualStepS P s Δo Tm β hβ hβc i hp₁) (D₂ : DualStepS P s Δo Tm β hβ hβc (i + 1) hp₂)
    (hC : RetainedHomotopyStep D₁.cup D₂.cup) (htr : D₂.tr = D₁.tr) (hO : D₂.orth = D₁.orth)
    (hz : D₂.zP = D₁.zR) :
    pairedFun D₂.R.I.toPlaceRetentionG.toRetainedPairing.QP D₂.tr D₂.R.zP =
      pairedFun D₁.R.I.toPlaceRetentionG.toRetainedPairing.QR D₁.tr D₁.R.zS := by
  obtain ⟨cup₁, tr₁, htr₁, O₁, zR₁, zP₁, b₁, hn₁⟩ := D₁
  obtain ⟨cup₂, tr₂, htr₂, O₂, zR₂, zP₂, b₂, hn₂⟩ := D₂
  dsimp only at htr hO hz hC
  subst htr hO
  exact StepRetention.ofDual_consecutive hp₁ hp₂ cup₁ cup₂ hC tr₂ htr₂ O₂ zR₁ zP₁ _ b₁ hn₁ zR₂ zP₂
    _ b₂ hn₂ hz

variable [∀ s, DecidableEq (Places C.K (P.S₀ s))]

/-- **`hP` at the step `i + 1` from `hR` at the step `i`** (tex 4159, 4164–4174, 4185–4193):
on a genuine stage chain on `stagedCx P s`, the primitive functional of the state `i + 1` is the
relaxed functional of the step `i` (`cmState`), so lane RC32's pin `hR` at the step `i` for the
retention `D₁.R` gives the pin `hP` at the step `i + 1` for `D₂.R` (`DualStepS.consecutive`).
Kind: PROVED. -/
theorem DualStepS.hP_succ {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {m0 m1 m2 : ℕ}
    (gs : GenuineStageSteps C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s)
      (famX P s) (famEU P s) s m0 m1 m2 P.pidx P.ps.length)
    {i : ℕ} (hi : i + 1 < P.ps.length)
    (D₁ : DualStepS P s Δo Tm β hβ hβc i (gs.hnew i (by omega)))
    (D₂ : DualStepS P s Δo Tm β hβ hβc (i + 1) (gs.hnew (i + 1) hi))
    (hC : RetainedHomotopyStep D₁.cup D₂.cup) (htr : D₂.tr = D₁.tr) (hO : D₂.orth = D₁.orth)
    (hz : D₂.zP = D₁.zR)
    (hR : gs.lamR i = pairedFun D₁.R.I.toPlaceRetentionG.toRetainedPairing.QR D₁.tr D₁.R.zS) :
    (cmState (gs.toChainM h28 hI hInj) (i + 1) hi.le).lam =
      pairedFun D₂.R.I.toPlaceRetentionG.toRetainedPairing.QP D₂.tr D₂.R.zP :=
  hR.trans (DualStepS.consecutive D₁ D₂ hC htr hO hz).symm

end Step

section Global

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ) (s : ℕ)

/-- The transported conditions of the support `T` at the stage `s` (tex 3740–3745).
Kind: definition. -/
abbrev pairedCondS (T : Finset P.ι) :=
  presCondS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
    (famX' P s s) (famEU' P s s) T

/-- The Selmer data of the transported presentation at the support `T` (tex 3740–3745).
Kind: definition. -/
abbrev pairedDataS (T : Finset P.ι) : SelData (StageRing s) :=
  suppDataS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
    (famX' P s s) (famEU' P s s) T

/-- The global cochains of the paired module (tex 3740–3745). Kind: definition. -/
abbrev pairedGlobS : GCx (StageRing s) := globalCx (StageRing s) (GKS C.K (P.S s)) (famM' P s s)

/-- The restriction of the paired module to the places of the presentation (tex 3740–3745).
Kind: definition. -/
abbrev pairedResS :=
  resS (StageRing s) (GKS C.K (P.S s)) (presGv C.K (P.S₀ s) (P.S s) (P.place s))
    (presLoc C.K (P.S₀ s) (P.S s) (P.place s)) (famM' P s s)

/-- **The transported norm identity from a transported global identity** (tex 4169–4171,
3740–3745): as lane E2's `gxClass_step_of_global`, for global classes `g_R`, `g_T` of the paired
module with local lifts `u_R`, `u_T` at the transported conditions, `g_R = e g_T + d b_G` gives
`(g_R, u_R, 0) = e · i'(g_T, u_T, 0) + d b` in the transported presentation (lane E2's
`hnorm_changeIncl`, `exists_presLift₀`, `presι_injective`). Kind: PROVED. -/
theorem pairedNorm_of_global (i : ℕ)
    (hinj : ∀ v₀, Function.Injective (((famCondsT P s s).i v₀).f 1 1 rfl))
    (hsurj : ∀ v₀, Function.Surjective (((famCondsT P s s).i v₀).f 0 0 rfl))
    (gR gT : (pairedGlobS P s).X 1)
    (uR : (piCx (pairedCondS P s (insert (P.pidx i) (chainT P.pidx i))).U).X 1)
    (uT : (piCx (pairedCondS P s (chainT P.pidx i)).U).X 1)
    (huR : (piMap (pairedCondS P s (insert (P.pidx i) (chainT P.pidx i))).i).f 1 1 rfl uR =
      (pairedResS P s).f 1 1 rfl gR)
    (huT : (piMap (pairedCondS P s (chainT P.pidx i)).i).f 1 1 rfl uT =
      (pairedResS P s).f 1 1 rfl gT)
    (e : StageRing s) (bG : (pairedGlobS P s).X 0)
    (hG : gR = e • gT + (pairedGlobS P s).d 0 1 rfl bG) :
    ∃ b : (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
        (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).X 0,
      (((gR, uR, 0) : selT (pairedDataS P s (insert (P.pidx i) (chainT P.pidx i))) 1) :
          (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s)
            (P.place s) (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).X 1) =
        e • (suppInclS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s)
            (P.place s) (famX' P s s) (famEU' P s s) (chainT P.pidx i) (P.pidx i)).f 1 1 rfl
          (((gT, uT, 0) : selT (pairedDataS P s (chainT P.pidx i)) 1) :
            (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s)
              (P.place s) (famX' P s s) (famEU' P s s) (chainT P.pidx i)).X 1) +
        (suppCxS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s) (P.place s)
          (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i))).d 0 1 rfl b := by
  obtain ⟨bU, hbU⟩ := exists_presLift₀ C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s)
    (famCondsT P s s) (P.place s) (famX' P s s) (famEU' P s s)
    (insert (P.pidx i) (chainT P.pidx i)) hsurj (pairedEU_surjective₀ P s)
    ((pairedResS P s).f 0 0 rfl bG)
  exact ⟨((bG, bU, 0) : selT (pairedDataS P s (insert (P.pidx i) (chainT P.pidx i))) 0),
    hnorm_changeIncl (presCondInclS C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s)
      (famCondsT P s s) (P.place s) (famX' P s s) (famEU' P s s) (chainT P.pidx i) (P.pidx i))
      gR gT uR uT e bG bU
      (presι_injective C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) (famCondsT P s s)
        (P.place s) (famX' P s s) (famEU' P s s) (insert (P.pidx i) (chainT P.pidx i)) hinj)
      huR huT hG hbU⟩

omit [(Ecurve ℓ).IsElliptic] in
/-- **The factor at `π⁻¹` is the factor at `π`** (tex 4171, `e_q^c = e_q`): lane E2's
`pointFactor_paired` at the stage `s`. Kind: PROVED. -/
theorem leafFactor_paired (a : StageRing s) (g : GKS C.K (P.S₀ s)) :
    pointFactor a ((@eK (StageRing s) _ s (stageIsoA s)).symm (P.alphaF' s s g : Acoef s))
        ((@eK (StageRing s) _ s (stageIsoA s)).symm
          (((P.alphaF' s s g)⁻¹ : (Acoef s)ˣ) : Acoef s)) =
      pointFactor a ((@eK (StageRing s) _ s (stageIsoA s)).symm (P.alphaF s s g : Acoef s))
        ((@eK (StageRing s) _ s (stageIsoA s)).symm
          (((P.alphaF s s g)⁻¹ : (Acoef s)ˣ) : Acoef s)) :=
  @pointFactor_paired C.K _ _ (P.S₀ s) s (P.sh s) _ (P.hs s) (P.hs0 s) _ _ (P.ξ s) (P.ψf s s)
    (StageRing s) _ (stageIsoA s) a g

end Global


section Assembly

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  {P : StagedPresentation C D Fam x Ψ} {s : ℕ}
  {Δo : LocalConditions (StageRing s) (GKS C.K (P.S s))
    (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
    (famM' P s s)}
  {Tm : Type} [AddCommGroup Tm] [Module (StageRing s) Tm] [DistribMulAction (GKS C.K (P.S s)) Tm]
  [SMulCommClass (GKS C.K (P.S s)) (StageRing s) Tm] [TopologicalSpace Tm] [ContinuousAdd Tm]
  [ContinuousConstSMul (StageRing s) Tm] [ContinuousSMul (GKS C.K (P.S s)) Tm]
  {β : famM' P s s →ₗ[StageRing s] famM P s s →ₗ[StageRing s] Tm}
  {hβ : ∀ (g : GKS C.K (P.S s)) (a : famM' P s s) (b : famM P s s), β (g • a) (g • b) = g • β a b}
  {hβc : Continuous fun y : famM' P s s × famM P s s => β y.1 y.2}

/-- **The inputs of a step from a transported global identity** (tex 4157–4175, 3740–3745):
the transported classes are `(g_R, u_R, 0)` and `(g_T, u_T, 0)`, the boundary and the norm
identity are those of `pairedNorm_of_global` at the leaf's point factor; at a positive stage
`hinj`, `hsurj` are `pairedConds_injective`, `pairedConds_surjective₀`. Consecutive steps whose
global classes and lifts agree have consecutive transported classes (definitionally).
Kind: definition. -/
def DualStepS.ofGlobal {i : ℕ} {hp : P.pidx i ∉ chainT P.pidx i}
    (cup : DualCupInputs C.K (P.S₀ s) (P.S s) (StageRing s) (famM P s s) (famConds P s s)
      (P.place s) (famX P s s) (famEU P s s) (famM' P s s) Δo (famX' P s s) (famEU' P s s) Tm β
      hβ hβc (chainT P.pidx i) (P.pidx i) hp)
    (tr : (coneCx (dualCupResE C.K (P.S₀ s) (P.S s) (StageRing s) (P.place s) Tm)).X 3
      →ₗ[StageRing s] StageRing s)
    (htr : ∀ y, tr ((coneCx (dualCupResE C.K (P.S₀ s) (P.S s) (StageRing s) (P.place s)
      Tm)).d 2 3 rfl y) = 0)
    (orth : OrthComparisonInverse C.K (P.S₀ s) (P.S s) (StageRing s) (famM' P s s) Δo
      (famCondsT P s s) (P.place s) (famX' P s s) (famEU' P s s))
    (hinj : ∀ v₀, Function.Injective (((famCondsT P s s).i v₀).f 1 1 rfl))
    (hsurj : ∀ v₀, Function.Surjective (((famCondsT P s s).i v₀).f 0 0 rfl))
    (gR gT : (pairedGlobS P s).X 1)
    (uR : (piCx (pairedCondS P s (insert (P.pidx i) (chainT P.pidx i))).U).X 1)
    (uT : (piCx (pairedCondS P s (chainT P.pidx i)).U).X 1)
    (huR : (piMap (pairedCondS P s (insert (P.pidx i) (chainT P.pidx i))).i).f 1 1 rfl uR =
      (pairedResS P s).f 1 1 rfl gR)
    (huT : (piMap (pairedCondS P s (chainT P.pidx i)).i).f 1 1 rfl uT =
      (pairedResS P s).f 1 1 rfl gT)
    (bG : (pairedGlobS P s).X 0)
    (hG : gR = leafFactorS P s i • gT + (pairedGlobS P s).d 0 1 rfl bG) :
    DualStepS P s Δo Tm β hβ hβc i hp where
  cup := cup
  tr := tr
  htr := htr
  orth := orth
  zR := ((gR, uR, 0) : selT (pairedDataS P s (insert (P.pidx i) (chainT P.pidx i))) 1)
  zP := ((gT, uT, 0) : selT (pairedDataS P s (chainT P.pidx i)) 1)
  b := Classical.choose (pairedNorm_of_global P s i hinj hsurj gR gT uR uT huR huT _ bG hG)
  hnorm := Classical.choose_spec
    (pairedNorm_of_global P s i hinj hsurj gR gT uR uT huR huT _ bG hG)

end Assembly

end ZInQ.Manuscript.RC.Wiring
