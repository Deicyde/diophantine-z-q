import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Realized
import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Arithmetic

/-!
**Theorem 5.3, Lane RC0 round 15: the split projection at the new primes as a homotopy
equivalence**

Lemma `ex:limits-inner-limit` (tex 4391–4451, normalized retract data tex 4423–4437) and the split
local model at the new prime `q_i` (tex 4859–4873). The link `projection_model` of
`ILStageStepFamilyLinked` asserts a quasi-isomorphism over `A_i` on a `U`-large set of positive
stages; eventuality weakens the stage quantifier, not the coefficient ring, and the genuine label
precision must cover `A_i`. The supplied same-stage trivial-action and fixed-root hypotheses and
the normalized retract prove the stronger property constructed here: at every positive stage, a
homotopy equivalence of the local cochains at `q_i` with the split model whose forward map is the
projection of the stage record.

* `retractProjectionEquiv`: a normalized retract of `X` onto `Y` is a homotopy equivalence
  `X ≃ Y` with forward map its projection (`GRetract.homotopyEquiv` reversed). PROVED.
* `orientedRetractionEquiv`: the same for the RC53 group's `OrientedLocalRetraction`; in every
  degree its forward map is the oriented local projection `localProjectionAt`. PROVED.
  `stage_projection_model_of_oriented`: the stage form of the link. PROVED.
* `exists_stagePairing_trace_retract`: the RC53 group's stage pairing producer
  `exists_stagePairing_trace`, keeping the normalized local retract whose projection is the split
  projection. Same inputs. PROVED.
* `exists_split_projectionModel`: a split-stage record together with a normalized retract with
  its projection, from the inputs of `StageArithmeticInput.exists_split`. PROVED.
* `exists_stagePairing_trace_transport`, `exists_split_traceModel`: the same, keeping also the
  original trace and the trace transport of `exists_relativeSplitPair_trace_duality`; its
  original side is `originalCupTrace`; the steps are `exists_split_trace_of_allPlace` and
  `exists_split_trace_of_original`. PROVED.
* `producedStagesModel`: the produced split stages, chosen with that retract and transport;
  `producedStagesModel_projection_model`: the link, in the form of the argument `hproj` of
  `ILStageStepFamilyLinked.ofAssembled`. PROVED. `producedStagesModel_trace_transport`: the
  trace transport for the chosen records. PROVED.
* `assemble_realized_of_stages`: the realized assembly on any split-stage family.
  `assemble_inner_limit_realized_model`, `assemble_from_support_change_realized_model`: the
  realized assemblies on `producedStagesModel`, with the link. No input is added. PROVED.
* `zeroSplitStage_projection_model`: the link also holds at the zero stage. PROVED.
* `JAt_eq_conjMatrix_of_rational_curve`: the argument `hJ` of `ofAssembled` for a curve over
  the rationals, from the integral identification of the retained Tate matrix (the step inside
  `RetainedLocalArithmetic.hloc_at_rational_curve`). PROVED.
  `conjMatrixK_lift_sq`, `conjMatrixK_lift_det`: the inputs `hJ`, `hJdet` of
  `RetainedLocalArithmetic.of_splitStages` for that matrix. PROVED.

The existing `producedStages` statement does not export a local projection equivalence or
identify its chosen record with the normalized retract witness. `producedStagesModel` supplies
these guarantees by choosing from the strengthened statement. No logical non-derivability theorem
for the old family is asserted here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain IsLocalRing Module
open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (GRetract Lambda StageA stageIdeal residualCohomologyAt)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages Vec2)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange

/-! **Normalized retracts and their projections** -/

section Retract

variable {A : Type} [CommRing A] {X Y : GCx A}

/-- **The projection of a normalized retract is a homotopy equivalence** `X ≃ Y`, with forward
map the projection `p` and inverse the inclusion `i` (`GRetract.homotopyEquiv` reversed;
tex 4423–4437). Kind: definition (PROVED identities). -/
def retractProjectionEquiv (R : GRetract X Y) : HomotopyEquiv X.toCC Y.toCC :=
  R.homotopyEquiv.symm

/-- The forward map is the projection. Kind: PROVED. -/
theorem retractProjectionEquiv_hom (R : GRetract X Y) :
    (retractProjectionEquiv R).hom = GHom.toCC R.p :=
  rfl

/-- The inverse is the inclusion. Kind: PROVED. -/
theorem retractProjectionEquiv_inv (R : GRetract X Y) :
    (retractProjectionEquiv R).inv = GHom.toCC R.i :=
  rfl

/-- **The link of a normalized retract**: a homotopy equivalence with forward map its
projection. Kind: PROVED. -/
theorem retract_projection_model (R : GRetract X Y) :
    ∃ e : HomotopyEquiv X.toCC Y.toCC, e.hom = GHom.toCC R.p :=
  ⟨retractProjectionEquiv R, rfl⟩

end Retract

/-! **The oriented local retraction** -/

section Oriented

variable {A G M : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {e : M ≃ₗ[A] Vec2 A} {φ σ : G} {c₂ : (contCochains A G M).X 2 →ₗ[A] M}

/-- **An oriented local retraction is a homotopy equivalence of the local cochains with the
split model**, with forward map its projection (tex 4423–4437, 4859–4868). Kind: definition
(PROVED identities). -/
def orientedRetractionEquiv (R : OrientedLocalRetraction e φ σ c₂) :
    HomotopyEquiv (natCx (contCochains A G M)).toCC (splitLocalComplex A).toCC :=
  retractProjectionEquiv R.retract

/-- The forward map is the projection of the retraction. Kind: PROVED. -/
theorem orientedRetractionEquiv_hom (R : OrientedLocalRetraction e φ σ c₂) :
    (orientedRetractionEquiv R).hom = GHom.toCC R.retract.p :=
  rfl

/-- In every degree the forward map is the oriented local projection: evaluation in degree zero,
the pair `(φ, σ)` in degree one and the normalized coordinate `c₂` in degree two. Kind: PROVED. -/
theorem orientedRetractionEquiv_hom_apply (R : OrientedLocalRetraction e φ σ c₂) (n : ℤ)
    (z : (natCx (contCochains A G M)).X n) :
    ((orientedRetractionEquiv R).hom.f n).hom z = localProjectionAt e φ σ c₂ n z :=
  R.projection n z

end Oriented

/-! **The stage form of the link** -/

section StageLocal

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)]

omit [W.IsElliptic] in
/-- **The link from an oriented local retraction of the family's local cochains at `q_i`**, in
the form of the field `projection_model` (tex 4859–4868). Kind: PROVED. -/
theorem stage_projection_model_of_oriented (F : ActualStageFamily S₀ W α) (i : ℕ)
    {e : ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i) ≃ₗ[Acoef i] Vec2 (Acoef i)}
    {φ σ : Gloc K (F.q i)}
    {c₂ : (contCochains (Acoef i) (Gloc K (F.q i))
      (ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i))).X 2 →ₗ[Acoef i]
        ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i)}
    (R : OrientedLocalRetraction e φ σ c₂) :
    ∃ e' : HomotopyEquiv (F.localCx i).toCC (splitLocalComplex (StageA i)).toCC,
      e'.hom = GHom.toCC R.retract.p :=
  ⟨orientedRetractionEquiv R, rfl⟩

end StageLocal

/-! **The stage pairing producer, keeping the local retract** -/

section StagePairing

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))
  (Dold : SelData (Acoef i)) (Qold : SelPairData Dold Dold) (Tq Uq : GCx (Acoef i))
  (rq : GHom Dold.G (actualStageLocalCx W i α q)) (sq : GHom Qold.E Tq)
  (ιq : GHom Uq (actualStageLocalCx W i α q))
  (Pq : GPair (actualStageLocalCx W i α q) (actualStageLocalCx W i α q) Tq)
  (V : RetainedPlaceInput Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq)
  (trAll : (coneCx (allTargetRes Dold Qold Tq sq)).X 3 →ₗ[Acoef i] Acoef i)
  (htrAll : ∀ z, trAll ((coneCx (allTargetRes Dold Qold Tq sq)).d 2 3 rfl z) = 0)

/-- **The stage pairing producer with its local retract**: the inputs and the construction of
`exists_stagePairing_trace` (the oriented local retraction of
`exists_stageOrientedLocalRetraction`, then `exists_relativeSplitPair_trace_duality`), with the
normalized retract kept; the split projection is its projection `R.p` (tex 4385–4451,
4859–4873). Kind: PROVED. -/
theorem exists_stagePairing_trace_retract
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n) = splitLocalRank n)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll))) :
    ∃ (R : GRetract (actualStageLocalCx W i α q) (splitLocalComplex (Acoef i)))
      (Q : SelPairData
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) R.p)
          Uq (ghomComp ιq R.p))
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) R.p)
          Uq (ghomComp ιq R.p)))
      (tr : (coneCx Q.resE).X 3 →ₗ[Acoef i] Acoef i)
      (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) := by
  obtain ⟨_, _, _, _, R, _⟩ := exists_stageOrientedLocalRetraction (K := K) (S := S)
    W i α q h2 hW htriv hμ hfin hdim
  obtain ⟨Q, tr, htr, hdual, _⟩ :=
    exists_relativeSplitPair_trace_duality Dold Qold (actualStageLocalCx W i α q)
      Tq Uq rq sq ιq Pq V trAll htrAll R.retract hG hL
  exact ⟨R.retract, Q, tr, htr, hdual⟩

/-- **The stage pairing producer with its local retract and the trace transport**: as
`exists_stagePairing_trace_retract`, keeping also the last conjunct of
`exists_relativeSplitPair_trace_duality`: on split cochains the produced trace of the produced
local cup is the given all-place trace of the original local cup `Pq` of the included cochains
(tex 4385–4451, 4438–4442). Kind: PROVED. -/
theorem exists_stagePairing_trace_transport
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n) = splitLocalRank n)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll))) :
    ∃ (R : GRetract (actualStageLocalCx W i α q) (splitLocalComplex (Acoef i)))
      (Q : SelPairData
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) R.p)
          Uq (ghomComp ιq R.p))
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) R.p)
          Uq (ghomComp ιq R.p)))
      (tr : (coneCx Q.resE).X 3 →ₗ[Acoef i] Acoef i)
      (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) ∧
      ∀ (a b : ℤ) (h : a + b = 2) (u : (splitLocalComplex (Acoef i)).X a)
        (v : (splitLocalComplex (Acoef i)).X b),
        tr (0, Q.cupL.P a b 2 h u v) =
          trAll (0, 0, Pq.P a b 2 h (R.i.f a a rfl u) (R.i.f b b rfl v)) := by
  obtain ⟨_, _, _, _, R, _⟩ := exists_stageOrientedLocalRetraction (K := K) (S := S)
    W i α q h2 hW htriv hμ hfin hdim
  obtain ⟨Q, tr, htr, hdual, htrace⟩ :=
    exists_relativeSplitPair_trace_duality Dold Qold (actualStageLocalCx W i α q)
      Tq Uq rq sq ιq Pq V trAll htrAll R.retract hG hL
  exact ⟨R.retract, Q, tr, htr, hdual, htrace⟩

end StagePairing

/-! **Split stages with the link** -/

section SplitModel

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)] [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}

/-- **A split-stage record with a normalized retract of the local cochains whose projection is
the record's projection**, from the inputs of `StageArithmeticInput.exists_split` and by its
construction, through `exists_stagePairing_trace_retract` (tex 4385–4451, 4859–4873, 5035–5071).
Kind: PROVED. -/
theorem exists_split_projectionModel {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ s : SplitStage F i S.retainedCondition S.condition,
      ∃ Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)), Rt.p = s.projection := by
  obtain ⟨trN, htrN, hGN, hLN⟩ := O.exists_original_trace_duality i p hK hS₀ h2
    S.otherOld S.otherDerivatives S.originalIsotropy
  let Qall := allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
    S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained
  let N := O.pair i S.originalIsotropy
  let trAll := pullScalarTrace Qall N S.originalComparison.scalar trN
  let htrAll := pullScalarTrace_kills Qall N S.originalComparison.scalar trN htrN
  have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
  obtain ⟨hG, hL⟩ := OriginalDiagramComparison.duality Qall N S.originalComparison
    trN htrN hGN hLN
  obtain ⟨Rt, Q, tr, htr, hdual⟩ := exists_stagePairing_trace_retract W i (F.character i)
    (F.q i) (F.datum i) S.oldPair S.scalarLocal S.retainedCondition (F.restriction i)
    S.scalarRestriction S.condition S.localCup S.retained trAll htrAll
    (F.odd i) (F.fullTorsion i) S.trivialAction S.fixedRoots
    (F.local_residual_finite p.localFinite i) S.localDimensions hG hL
  exact ⟨⟨Rt.p, Q, tr, htr, hdual⟩, Rt, rfl⟩

/-- **The original side of the trace transport**: the original trace `trN`, through the original
scalar comparison, of the original retained local cup of two included split cochains
(tex 4385–4388, 4438–4442). Kind: definition. -/
def originalCupTrace {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i)
    (trN : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i)
    (Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i))) (m n : ℤ) (h : m + n = 2)
    (u : (splitLocalComplex (Acoef i)).X m) (v : (splitLocalComplex (Acoef i)).X n) :
    Acoef i :=
  let trAll : (coneCx (allTargetRes (F.datum i) S.oldPair S.scalarLocal
      S.scalarRestriction)).X 3 →ₗ[Acoef i] Acoef i :=
    pullScalarTrace (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
      S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup
      S.retained) (O.pair i S.originalIsotropy) S.originalComparison.scalar trN
  trAll (0, 0, S.localCup.P m n 2 h (Rt.i.f m m rfl u) (Rt.i.f n n rfl v))

/-- **A split-stage record with its retract and the trace transport, from all-place duality**:
for any all-place trace `trAll` of the original retained diagram with both duality statements,
the construction of `exists_split_projectionModel`, keeping the transport identity of
`exists_stagePairing_trace_transport` (tex 4385–4451, 4438–4442). Kind: PROVED. -/
theorem exists_split_trace_of_allPlace {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K)
    (trAll : (coneCx (allTargetRes (F.datum i) S.oldPair S.scalarLocal
      S.scalarRestriction)).X 3 →ₗ[Acoef i] Acoef i)
    (htrAll : ∀ z, trAll ((coneCx (allTargetRes (F.datum i) S.oldPair S.scalarLocal
      S.scalarRestriction)).d 2 3 rfl z) = 0)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal S.retainedCondition
        (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained) trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal S.retainedCondition
        (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained) trAll htrAll))) :
    ∃ s : SplitStage F i S.retainedCondition S.condition,
      ∃ Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)), Rt.p = s.projection ∧
        ∀ (m n : ℤ) (h : m + n = 2) (u : (splitLocalComplex (Acoef i)).X m)
          (v : (splitLocalComplex (Acoef i)).X n),
          s.trace (0, s.pairing.cupL.P m n 2 h u v) =
            trAll (0, 0, S.localCup.P m n 2 h (Rt.i.f m m rfl u) (Rt.i.f n n rfl v)) := by
  obtain ⟨Rt, Q, tr, htr, hdual, htrace⟩ := exists_stagePairing_trace_transport W i
    (F.character i) (F.q i) (F.datum i) S.oldPair S.scalarLocal S.retainedCondition
    (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained trAll htrAll
    (F.odd i) (F.fullTorsion i) S.trivialAction S.fixedRoots
    (F.local_residual_finite p.localFinite i) S.localDimensions hG hL
  exact ⟨⟨Rt.p, Q, tr, htr, hdual⟩, Rt, rfl, htrace⟩

/-- **A split-stage record with its retract and the trace transport, from the original trace**:
`exists_split_trace_of_allPlace` for the original trace pulled back along the original scalar
comparison, whose all-place duality is `OriginalDiagramComparison.duality` (tex 4385–4451,
4438–4442). Kind: PROVED. -/
theorem exists_split_trace_of_original {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K)
    (trN : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htrN : ∀ z, trN ((coneCx (O.pair i S.originalIsotropy).resE).d 2 3 rfl z) = 0)
    (hGN : QuasiIso (GHom.toCC (globalDualityMap (O.pair i S.originalIsotropy) trN htrN)))
    (hLN : QuasiIso (GHom.toCC (localDualityMap (O.pair i S.originalIsotropy) trN htrN))) :
    ∃ s : SplitStage F i S.retainedCondition S.condition,
      ∃ Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)), Rt.p = s.projection ∧
        ∀ (m n : ℤ) (h : m + n = 2) (u : (splitLocalComplex (Acoef i)).X m)
          (v : (splitLocalComplex (Acoef i)).X n),
          s.trace (0, s.pairing.cupL.P m n 2 h u v) = originalCupTrace S trN Rt m n h u v := by
  have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
  have hd := OriginalDiagramComparison.duality
    (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
      S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained)
    (O.pair i S.originalIsotropy) S.originalComparison trN htrN hGN hLN
  exact exists_split_trace_of_allPlace S p
    (pullScalarTrace (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
      S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained)
      (O.pair i S.originalIsotropy) S.originalComparison.scalar trN)
    (pullScalarTrace_kills (allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
      S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained)
      (O.pair i S.originalIsotropy) S.originalComparison.scalar trN htrN) hd.1 hd.2

/-- **A split-stage record with its retract, the original trace and the trace transport**: as
`exists_split_projectionModel`, keeping also the original trace `trN` of
`OldDualityData.exists_original_trace_duality` with its two duality statements, and the
identity: on split cochains the record's trace of its local cup is `originalCupTrace`
(tex 4385–4451, 4438–4442, 5035–5071). Kind: PROVED. -/
theorem exists_split_traceModel {i : ℕ} [NeZero i] (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ s : SplitStage F i S.retainedCondition S.condition,
      ∃ Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)), Rt.p = s.projection ∧
        ∃ (trN : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i)
          (htrN : ∀ z, trN ((coneCx (O.pair i S.originalIsotropy).resE).d 2 3 rfl z) = 0),
          QuasiIso (GHom.toCC (globalDualityMap (O.pair i S.originalIsotropy) trN htrN)) ∧
          QuasiIso (GHom.toCC (localDualityMap (O.pair i S.originalIsotropy) trN htrN)) ∧
          ∀ (m n : ℤ) (h : m + n = 2) (u : (splitLocalComplex (Acoef i)).X m)
            (v : (splitLocalComplex (Acoef i)).X n),
            s.trace (0, s.pairing.cupL.P m n 2 h u v) = originalCupTrace S trN Rt m n h u v := by
  have hex := O.exists_original_trace_duality i p hK hS₀ h2
    S.otherOld S.otherDerivatives S.originalIsotropy
  exact hex.elim fun trN h₁ => h₁.elim fun htrN hd =>
    (exists_split_trace_of_original S p trN htrN hd.1 hd.2).imp fun s hs =>
      hs.imp fun Rt hRt => ⟨hRt.1, trN, htrN, hd.1, hd.2, hRt.2⟩

variable {R : StandardOldReference S₀ W α} {width : ℕ}

/-- **The produced split stages, chosen with the retract**: no arithmetic input at stage zero
(`zeroSplitStage`); at a positive stage a record of `exists_split_traceModel`. This is
`producedStages` with `Classical.choose` of the strengthened producer in place of
`Classical.choice` of `exists_split` (tex 4385–4451, 4859–4873). Kind: definition. -/
def producedStagesModel (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)
  | 0 => zeroSplitStage F _ _
  | i + 1 => Classical.choose (exists_split_traceModel (a.stage (i + 1)) p hK hS₀ h2)

/-- **The link for the produced stages chosen with the retract**, in the form of the argument
`hproj` of `ILStageStepFamilyLinked.ofAssembled` (tex 4859–4868). Kind: PROVED. -/
theorem producedStagesModel_projection_model (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC (splitLocalComplex (StageA i)).toCC,
      e.hom = GHom.toCC (producedStagesModel a p hK hS₀ h2 i).projection := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi.out
  obtain ⟨Rt, hRt, -⟩ := Classical.choose_spec
    (exists_split_traceModel (a.stage (j + 1)) p hK hS₀ h2)
  exact ⟨retractProjectionEquiv Rt, congrArg (fun f => GHom.toCC f) hRt⟩

/-- **The trace transport for the produced stages chosen with the retract**: at a positive stage
the retract of the link, the original trace with its two duality statements, and the identity
of `exists_split_traceModel` for the chosen record; the input from which the trace comparisons
`htrace02`, `htrace11`, `htrace20` of `RetainedZeroTwo.of_splitStages` and
`RetainedLocalArithmetic.of_splitStages` are to be matched (tex 4385–4451, 4860–4863).
Kind: PROVED. -/
theorem producedStagesModel_trace_transport (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) (j : ℕ) :
    ∃ Rt : GRetract (F.localCx (j + 1)) (splitLocalComplex (Acoef (j + 1))),
      Rt.p = (producedStagesModel a p hK hS₀ h2 (j + 1)).projection ∧
      ∃ (trN : (coneCx (O.pair (j + 1) (a.stage (j + 1)).originalIsotropy).resE).X 3
          →ₗ[Acoef (j + 1)] Acoef (j + 1))
        (htrN : ∀ z, trN ((coneCx (O.pair (j + 1)
          (a.stage (j + 1)).originalIsotropy).resE).d 2 3 rfl z) = 0),
        QuasiIso (GHom.toCC
          (globalDualityMap (O.pair (j + 1) (a.stage (j + 1)).originalIsotropy) trN htrN)) ∧
        QuasiIso (GHom.toCC
          (localDualityMap (O.pair (j + 1) (a.stage (j + 1)).originalIsotropy) trN htrN)) ∧
        ∀ (m n : ℤ) (h : m + n = 2) (u : (splitLocalComplex (Acoef (j + 1))).X m)
          (v : (splitLocalComplex (Acoef (j + 1))).X n),
          (producedStagesModel a p hK hS₀ h2 (j + 1)).trace
              (0, (producedStagesModel a p hK hS₀ h2 (j + 1)).pairing.cupL.P m n 2 h u v) =
            originalCupTrace (a.stage (j + 1)) trN Rt m n h u v :=
  Classical.choose_spec (exists_split_traceModel (a.stage (j + 1)) p hK hS₀ h2)

end SplitModel

/-! **The realized assembly with the link** -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)] [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}

/-- **The realized assembly on any split-stage family**: the proof of
`assemble_inner_limit_realized`, with the produced stages replaced by an arbitrary family `s` of
split-stage records over the same retained conditions (tex 4385–4451, 4976–5135). Kind:
PROVED. -/
theorem assemble_realized_of_stages (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W)
    (s : ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)) :
    ∃ L : AssembledLimit a U hU Cn hW, L.stages = s ∧ L.Realized := by
  obtain ⟨B, hbdd, hB⟩ := a.residualSupport.producerBounds p hK hS₀ h2
  obtain ⟨r₀, C, D, E, hrank, hlow, hhigh, hrankB, hev, hloc, hreal⟩ :=
    exists_retained_of_stageInputs_realized U hU (fun i => F.globalCx i)
      (F.flat hS₀ a.oldFlat) (retainedConditions a)
      (fun i => stageRes F i (s i).projection)
      (fun i => ghomComp (retainedInclusions a i) (s i).projection)
      (fun i => (s i).pairing) (fun i => (s i).trace)
      (fun i => (s i).trace_kills) (fun i => (s i).duality)
      (a.residualSupport.residual_finite p hS₀ h2) 0 3 hbdd B hB
  have hbound : ∀ n, C.rank n ≤ B := by
    intro n
    rw [hrank]
    exact hrankB n
  have hranks : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
      C.rank n = Module.finrank (ResidueField (StageA i))
        (residualCohomologyAt (F.globalCx i) n) := by
    filter_upwards [hev] with i hi
    intro _ n
    rw [hrank]
    exact hi n
  have hcertificate : FibreCertificates hU Cn hW D := by
    intro P _ ε₀ ε₂ ε σ hε₂ hε hσ hl
    exact fibreInnerLimitPairingCertificate_of_retained hU E P Cn W hW
      ε₀ ε₂ ε σ hε₂ hε hσ hl
  exact ⟨⟨B, s, C, D, E, hlow, hhigh, hbound, hranks, hloc, hcertificate⟩, rfl, hreal⟩

/-- **The realized assembly on the produced stages chosen with the retract, with the link**:
the assembled limit has stages `producedStagesModel`, is realized, and its split projections are
homotopy equivalences, in the form of the arguments `L`, `hL`, `hproj` of
`ILStageStepFamilyLinked.ofAssembled`. No input beyond those of `assemble_inner_limit_realized`
(tex 4385–4451, 4859–4873, 4976–5135). Kind: PROVED. -/
theorem assemble_inner_limit_realized_model (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ L : AssembledLimit a U hU Cn hW,
      L.stages = producedStagesModel a p hK hS₀ h2 ∧ L.Realized ∧
      ∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC
        (splitLocalComplex (StageA i)).toCC, e.hom = GHom.toCC (L.stages i).projection := by
  obtain ⟨L, hs, hL⟩ := assemble_realized_of_stages p hK hS₀ h2 a U hU Cn hW
    (producedStagesModel a p hK hS₀ h2)
  refine ⟨L, hs, hL, ?_⟩
  intro i _
  rw [hs]
  exact producedStagesModel_projection_model a p hK hS₀ h2 i

/-- **The support-change realized assembly on the produced stages chosen with the retract, with
the link**: `assemble_from_support_change_realized` with `producedStagesModel` (tex 3483–3498,
4385–4451, 4859–4873, 4976–5135). Kind: PROVED. -/
theorem assemble_from_support_change_realized_model (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R) (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) U hU Cn hW,
        L.stages = producedStagesModel (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6)
          p hK hS₀ h2 ∧ L.Realized ∧
        ∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC
          (splitLocalComplex (StageA i)).toCC, e.hom = GHom.toCC (L.stages i).projection := by
  let T := residualSupport_six_of_stage_dimensions F R p h788 hK hS₀ h2 P
    (fun i _ => (stage i).localDimensions)
  obtain ⟨L, hs, hL, hproj⟩ :=
    assemble_inner_limit_realized_model p hK hS₀ h2 ⟨oldFlat, T, stage⟩ U hU Cn hW
  exact ⟨T, L, hs, hL, hproj⟩

end Assembly

/-! **The zero stage** -/

section ZeroStage

variable {K : Type} [Field K] [NumberField K] {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ}
  [∀ i, IsOpenKer (α i)]

omit [W.IsElliptic] in
/-- **The link at the zero stage**: over the zero coefficient ring every cochain map is a
homotopy equivalence, so a field `projection_model` on `SplitStage` would hold at every stage
(tex 4391–4406). Kind: PROVED. -/
theorem zeroSplitStage_projection_model (F : ActualStageFamily S₀ W α)
    (Uq : GCx (Acoef 0)) (ιq : GHom Uq (F.localCx 0)) :
    ∃ e : HomotopyEquiv (F.localCx 0).toCC (splitLocalComplex (StageA 0)).toCC,
      e.hom = GHom.toCC (zeroSplitStage F Uq ιq).projection := by
  have : Subsingleton (Acoef 0) := stageA_zero_subsingleton
  refine ⟨{ hom := GHom.toCC (zeroSplitStage F Uq ιq).projection
            inv := GHom.toCC (zeroGHom _ _)
            homotopyHomInvId := Homotopy.ofEq ?_
            homotopyInvHomId := Homotopy.ofEq ?_ }, rfl⟩
  · ext n x
    exact (Module.subsingleton (Acoef 0) _).elim _ _
  · ext n x
    exact (Module.subsingleton (Acoef 0) _).elim _ _

end ZeroStage

/-! **The conjugation matrix at a fibre, for a curve over the rationals** -/

section RationalCurve

open ZInQ.Contrib.RC53Assist.ResidueIdentity (RetainedLocalArithmetic)
open scoped WeierstrassCurve

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}
  {D : RetainedLimitPairingStages U C}

/-- **The conjugation matrix of the retained local arithmetic at a fibre, for a curve over the
rationals**: from the integral identification of `X.J` with the realized Tate conjugation
matrix, `X.JAt P = conjMatrix Cn (B⁄K) hW P`, the type of the argument `hJ` of
`ILStageStepFamilyLinked.ofAssembled` (the step inside
`RetainedLocalArithmetic.hloc_at_rational_curve`; tex 2798–2805, 5027–5070). Kind: PROVED. -/
theorem JAt_eq_conjMatrix_of_rational_curve (X : RetainedLocalArithmetic U C D)
    (P : Ideal Lambda) [P.IsPrime]
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (B : WeierstrassCurve ℚ) [B.IsElliptic] [HasFullTwoTorsion K S (B⁄K)]
    (Cn : ActualConj K S) (hW : (B⁄K).map (Cn.κ : K →+* K) = B⁄K)
    (hJ : X.J = (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda)) :
    X.JAt P = conjMatrix Cn (B⁄K) hW P := by
  unfold RetainedLocalArithmetic.JAt
  rw [hJ, Matrix.map_map, conjMatrix_eq_conjMatrixK B Cn hW P]
  congr 1

/-- The lifted realized conjugation matrix is an involution: the input `hJ` of
`RetainedLocalArithmetic.of_splitStages` for `J = (conjMatrixK B Cn).map (algebraMap ℤ_[2] Λ)`
(tex 2803–2804). Kind: PROVED. -/
theorem conjMatrixK_lift_sq {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (B : WeierstrassCurve ℚ) [B.IsElliptic]
    [HasFullTwoTorsion K S (B⁄K)] (Cn : ActualConj K S) :
    (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda) *
      (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda) = 1 := by
  rw [← Matrix.map_mul, conjMatrixK_sq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The lifted realized conjugation matrix has determinant `−1`: the input `hJdet` of
`RetainedLocalArithmetic.of_splitStages` for the same matrix (tex 3095–3096). Kind: PROVED. -/
theorem conjMatrixK_lift_det {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (B : WeierstrassCurve ℚ) [B.IsElliptic]
    [HasFullTwoTorsion K S (B⁄K)] (Cn : ActualConj K S) :
    ((conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda)).det = -1 := by
  have h := RingHom.map_det (algebraMap ℤ_[2] Lambda) (conjMatrixK B Cn)
  rw [det_conjMatrixK, map_neg, map_one] at h
  exact h.symm

end RationalCurve

end ZInQ.Manuscript.RC.Wiring
