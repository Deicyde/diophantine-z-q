import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Realized
import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.FullTransport

/-!
# Projection and original trace links for the support-change assembly

The positive-stage producer retains its normalized local retraction, the
original compact trace and all local-cup trace transports. The stage choice
therefore preserves the projection homotopy equivalence and the zero/two,
one/one and two/zero trace identities against the same original trace.

Identification with an independently presented residue-arithmetic local cup is
a separate named cochain obligation. Such an identification is not inferred
from equal ranks, duality or an arbitrary compact-cohomology isomorphism.

Sources: `diophantine_zq.tex`, lines 4385–4451, 4859–4873 and 4976–5135.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange

open CategoryTheory Matrix NumberField IsDedekindDomain IsLocalRing Module
open TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (GRetract Lambda StageA stageIdeal stageMap residualCohomologyAt)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages Vec2)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
open ZInQ.Contrib.RC53Assist.ResidueIdentity (StageArithmeticData LocalArithmeticData)

/-- Kind: definition. The finite coefficient stage carries the same discrete
scalar topology as the residue-arithmetic presentation; tex 2723–2727, 4385–4451. -/
local instance linkedStage_topology (i : ℕ) : TopologicalSpace (StageA i) := ⊥

/-- Kind: PROVED. The retained finite-stage scalar topology is discrete;
tex 2723–2727, 4385–4451. -/
local instance linkedStage_discrete (i : ℕ) : DiscreteTopology (StageA i) := ⟨rfl⟩

/-- Kind: PROVED. The original two-power coefficient exponent is nonzero;
tex 2723–2727, 4860–4863. -/
local instance linkedExponent_neZero (i : ℕ) : NeZero (2 ^ i) :=
  ⟨pow_ne_zero i two_ne_zero⟩

section ProjectionLink

variable {A : Type} [CommRing A] {X Y : GCx A}

/-- Kind: PROVED. Reverse the homotopy equivalence of a normalized retract,
so that its forward map is the actual projection; tex 4423–4437. -/
def projectionEquivOfRetract (R : GRetract X Y) : HomotopyEquiv X.toCC Y.toCC :=
  R.homotopyEquiv.symm

/-- Kind: PROVED. The forward map of the projection equivalence is the
normalized retract's projection, not an independently chosen map;
tex 4423–4437. -/
theorem projectionEquivOfRetract_hom (R : GRetract X Y) :
    (projectionEquivOfRetract R).hom = GHom.toCC R.p := rfl

end ProjectionLink

section NativePairingLinks

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

/-- Kind: PROVED. Strengthen the native split pairing producer by keeping
its actual normalized local retraction and the full original local-cup trace
identity. No projection homotopy equivalence or trace transport is an input;
tex 4385–4451, 4859–4873. -/
theorem exists_stagePairing_trace_links
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n))
    (hdim : ∀ n, Module.finrank (ResidueField (Acoef i))
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
      (∃ e : HomotopyEquiv (actualStageLocalCx W i α q).toCC
        (splitLocalComplex (Acoef i)).toCC, e.hom = GHom.toCC R.p) ∧
      ∀ (a b : ℤ) (hab : a + b = 2) (u : (splitLocalComplex (Acoef i)).X a)
        (v : (splitLocalComplex (Acoef i)).X b),
        tr (0, Q.cupL.P a b 2 hab u v) =
          trAll (0, 0, Pq.P a b 2 hab (R.i.f a a rfl u) (R.i.f b b rfl v)) := by
  obtain ⟨_, _, _, _, Rt, _⟩ := exists_stageOrientedLocalRetraction (K := K) (S := S)
    W i α q h2 hW htriv hμ hfin hdim
  obtain ⟨Q, tr, htr, hdual, htrace⟩ := exists_relativeSplitPair_trace_duality
    Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V trAll htrAll
    Rt.retract hG hL
  exact ⟨Rt.retract, Q, tr, htr, hdual, ⟨projectionEquivOfRetract Rt.retract, rfl⟩, htrace⟩

end NativePairingLinks

section PositiveSplitLinks

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F} {i : ℕ} [NeZero i]

/-- Kind: definition. The original compact trace, pulled through the named
scalar comparison, of the actual retained local cup on the normalized
inclusion of the split cochains; tex 4385–4388, 4438–4442. -/
def originalCupTrace (S : StageArithmeticInput F O i)
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

/-- Kind: definition. Strengthened positive-stage output. The split stage,
normalized retraction and original compact trace are retained together, so
choice cannot discard their projection and trace links;
tex 4385–4451, 4859–4873. -/
structure LinkedSplitStage (S : StageArithmeticInput F O i) where
  /-- Kind: definition. The produced split-stage pairing and trace;
  tex 4385–4451. -/
  toSplitStage : SplitStage F i S.retainedCondition S.condition
  /-- Kind: definition. The actual normalized local retraction used to
  construct this stage; tex 4423–4437, 4859–4873. -/
  localRetract : GRetract (F.localCx i) (splitLocalComplex (Acoef i))
  /-- Kind: PROVED. The split projection is exactly the same retract's
  projection; tex 4423–4437, 4859–4873. -/
  projection_retract : localRetract.p = toSplitStage.projection
  /-- Kind: PROVED. The requested projection homotopy link, with the
  forward map fixed to this stage's projection; tex 4423–4437, 4859–4873. -/
  projection_model : ∃ e : HomotopyEquiv (F.localCx i).toCC
    (splitLocalComplex (Acoef i)).toCC, e.hom = GHom.toCC toSplitStage.projection
  /-- Kind: definition. The original compact trace before split replacement;
  tex 4385–4388, 5035–5071. -/
  originalTrace : (coneCx (O.pair i S.originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i
  /-- Kind: PROVED. The original trace kills compact coboundaries;
  tex 4385–4388, 5035–5071. -/
  originalTrace_kills : ∀ z,
    originalTrace ((coneCx (O.pair i S.originalIsotropy).resE).d 2 3 rfl z) = 0
  /-- Kind: PROVED. Original global duality for the retained trace;
  tex 4385–4388, 5055–5071. -/
  originalGlobalDuality : QuasiIso (GHom.toCC
    (globalDualityMap (O.pair i S.originalIsotropy) originalTrace originalTrace_kills))
  /-- Kind: PROVED. Original local duality for the retained trace;
  tex 4385–4388, 5055–5071. -/
  originalLocalDuality : QuasiIso (GHom.toCC
    (localDualityMap (O.pair i S.originalIsotropy) originalTrace originalTrace_kills))
  /-- Kind: PROVED. Full local-cup trace transport for this same original
  trace and inclusion; tex 4385–4388, 4438–4442. -/
  trace_transport : ∀ (a b : ℤ) (hab : a + b = 2)
    (u : (splitLocalComplex (Acoef i)).X a) (v : (splitLocalComplex (Acoef i)).X b),
    toSplitStage.trace (0, toSplitStage.pairing.cupL.P a b 2 hab u v) =
      originalCupTrace S originalTrace localRetract a b hab u v
  /-- Kind: PROVED. Zero/two specialization of the original transport;
  tex 4385–4388, 4860–4863. -/
  htrace02 : ∀ x y : Fin 2 → Acoef i,
    toSplitStage.trace (0, toSplitStage.pairing.cupL.P 0 2 2 rfl x y) =
      originalCupTrace S originalTrace localRetract 0 2 rfl x y
  /-- Kind: PROVED. One/one specialization of the original transport;
  tex 4385–4388, 4860–4863. -/
  htrace11 : ∀ x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i),
    toSplitStage.trace (0, toSplitStage.pairing.cupL.P 1 1 2 rfl x y) =
      originalCupTrace S originalTrace localRetract 1 1 rfl x y
  /-- Kind: PROVED. Two/zero specialization of the original transport;
  tex 4385–4388, 4860–4863. -/
  htrace20 : ∀ x y : Fin 2 → Acoef i,
    toSplitStage.trace (0, toSplitStage.pairing.cupL.P 2 0 2 rfl x y) =
      originalCupTrace S originalTrace localRetract 2 0 rfl x y

/-- Kind: PROVED. The original arithmetic construction supplies the
strengthened record, including its projection equivalence and all three
original trace transports. No new arithmetic hypothesis is introduced;
tex 4385–4451, 4859–4873, 5035–5071. -/
theorem StageArithmeticInput.exists_linked_split (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    Nonempty (LinkedSplitStage S) := by
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
  obtain ⟨Rt, Q, tr, htr, hdual, he, htrace⟩ := exists_stagePairing_trace_links W i
    (F.character i) (F.q i) (F.datum i) S.oldPair S.scalarLocal S.retainedCondition
    (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained trAll htrAll
    (F.odd i) (F.fullTorsion i) S.trivialAction S.fixedRoots
    (F.local_residual_finite p.localFinite i) S.localDimensions hG hL
  exact ⟨⟨⟨Rt.p, Q, tr, htr, hdual⟩, Rt, rfl, he, trN, htrN, hGN, hLN,
    htrace, htrace 0 2 rfl, htrace 1 1 rfl, htrace 2 0 rfl⟩⟩

/-- Kind: definition. Fix the strengthened positive-stage output once, with
its normalized projection and original trace retained; tex 4385–4451, 4859–4873. -/
def StageArithmeticInput.chosen_links (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    LinkedSplitStage S := Classical.choice (S.exists_linked_split p hK hS₀ h2)

end PositiveSplitLinks

section PreservedStageChoice

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}

/-- Kind: definition. Choose a strengthened positive-stage record once,
retaining its original trace and normalized retraction;
tex 4385–4451, 4859–4873. -/
def producedStageLinks' (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] : LinkedSplitStage (a.stage i) :=
  (a.stage i).chosen_links p hK hS₀ h2

/-- Kind: definition. Re-chosen split stages, forgetting the strengthened
record only after its witnesses have been fixed. The zero stage remains the
original zero-target stage; tex 4391–4406, 4385–4451, 4859–4873. -/
def producedStages' (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)
  | 0 => zeroSplitStage F _ _
  | i + 1 => (producedStageLinks' a p hK hS₀ h2 (i + 1)).toSplitStage

/-- Kind: PROVED. Every chosen positive-stage projection has the requested
homotopy equivalence with that exact forward map;
tex 4423–4437, 4859–4873. -/
theorem producedStages'_projection_model (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC
      (splitLocalComplex (Acoef i)).toCC,
      e.hom = GHom.toCC (producedStages' a p hK hS₀ h2 i).projection := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi.out
  exact (producedStageLinks' a p hK hS₀ h2 (j + 1)).projection_model

/-- Kind: definition. The original transport packet at a chosen positive
stage. It fixes the normalized projection and retains the original trace,
both original dualities and every local-cup trace identity;
tex 4385–4451, 4859–4873. -/
def OriginalStageTraceLinks (a : ArithmeticInputs F O R width)
    (s : ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i))
    (i : ℕ) [NeZero i] : Prop :=
  ∃ Rt : GRetract (F.localCx i) (splitLocalComplex (Acoef i)), Rt.p = (s i).projection ∧
    ∃ (trN : (coneCx (O.pair i (a.stage i).originalIsotropy).resE).X 3 →ₗ[Acoef i] Acoef i)
      (htrN : ∀ z, trN ((coneCx (O.pair i (a.stage i).originalIsotropy).resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC
        (globalDualityMap (O.pair i (a.stage i).originalIsotropy) trN htrN)) ∧
      QuasiIso (GHom.toCC
        (localDualityMap (O.pair i (a.stage i).originalIsotropy) trN htrN)) ∧
      ∀ (m n : ℤ) (hmn : m + n = 2) (u : (splitLocalComplex (Acoef i)).X m)
        (v : (splitLocalComplex (Acoef i)).X n),
        (s i).trace (0, (s i).pairing.cupL.P m n 2 hmn u v) =
          originalCupTrace (a.stage i) trN Rt m n hmn u v

/-- Kind: PROVED. Full original trace transport survives the stage choice,
with the exact normalized projection of the chosen split stage;
tex 4385–4451, 4859–4873. -/
theorem producedStages'_trace_transport (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i [NeZero i], OriginalStageTraceLinks a (producedStages' a p hK hS₀ h2) i := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi.out
  let B := producedStageLinks' a p hK hS₀ h2 (j + 1)
  exact ⟨B.localRetract, B.projection_retract, B.originalTrace, B.originalTrace_kills,
    B.originalGlobalDuality, B.originalLocalDuality, B.trace_transport⟩

/-- Kind: PROVED. The zero/two identity of the chosen stage against its
retained original trace. No independent choice of trace or inclusion occurs;
tex 4385–4388, 4860–4863. -/
theorem producedStages'_htrace02 (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] (x y : Fin 2 → Acoef i) :
    (producedStages' a p hK hS₀ h2 i).trace
      (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 0 2 2 rfl x y) =
      originalCupTrace (a.stage i) (producedStageLinks' a p hK hS₀ h2 i).originalTrace
        (producedStageLinks' a p hK hS₀ h2 i).localRetract 0 2 rfl x y := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne i)
  exact (producedStageLinks' a p hK hS₀ h2 (j + 1)).htrace02 x y

/-- Kind: PROVED. The one/one identity of the chosen stage against the
same original trace and inclusion; tex 4385–4388, 4860–4863. -/
theorem producedStages'_htrace11 (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] (x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i)) :
    (producedStages' a p hK hS₀ h2 i).trace
      (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 1 1 2 rfl x y) =
      originalCupTrace (a.stage i) (producedStageLinks' a p hK hS₀ h2 i).originalTrace
        (producedStageLinks' a p hK hS₀ h2 i).localRetract 1 1 rfl x y := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne i)
  exact (producedStageLinks' a p hK hS₀ h2 (j + 1)).htrace11 x y

/-- Kind: PROVED. The two/zero identity of the chosen stage against the
same original trace and inclusion; tex 4385–4388, 4860–4863. -/
theorem producedStages'_htrace20 (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] (x y : Fin 2 → Acoef i) :
    (producedStages' a p hK hS₀ h2 i).trace
      (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 2 0 2 rfl x y) =
      originalCupTrace (a.stage i) (producedStageLinks' a p hK hS₀ h2 i).originalTrace
        (producedStageLinks' a p hK hS₀ h2 i).localRetract 2 0 rfl x y := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne i)
  exact (producedStageLinks' a p hK hS₀ h2 (j + 1)).htrace20 x y

end PreservedStageChoice

section LinkedRealizedAssembly

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}
  {a : ArithmeticInputs F O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ Filter.cofinite} {Cn : ActualConj K S₀}
  {hW : W.map (Cn.κ : K →+* K) = W}

/-- Kind: definition. Projection homotopy and original trace links attached
to this assembled limit's exact stage family, not a second diagram;
tex 4385–4451, 4859–4873. -/
def AssembledLimit.StageLinks (L : AssembledLimit a U hU Cn hW) : Prop :=
  (∀ i [NeZero i], ∃ e : HomotopyEquiv (F.localCx i).toCC
    (splitLocalComplex (Acoef i)).toCC, e.hom = GHom.toCC (L.stages i).projection) ∧
    ∀ i [NeZero i], OriginalStageTraceLinks a L.stages i

/-- Kind: PROVED. Assemble on any prescribed split-stage family while
preserving the earlier actual global-complex realization. The finite-model,
retained pairing and certificates still use one set of witnesses;
tex 4385–4451, 4976–5135. -/
theorem assemble_realized_on_stages (p : ArithmeticPrints K)
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

/-- Kind: PROVED. Reassemble on the strengthened stage choice. Actual
global-complex realization, conditional certificates, normalized local
projection links and original trace transports refer to the same stages;
tex 4385–4451, 4859–4873, 4976–5135. -/
theorem assemble_inner_limit_realized' (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ L : AssembledLimit a U hU Cn hW,
      L.stages = producedStages' a p hK hS₀ h2 ∧ L.Realized ∧ L.StageLinks := by
  obtain ⟨L, hs, hreal⟩ := assemble_realized_on_stages p hK hS₀ h2 a U hU Cn hW
    (producedStages' a p hK hS₀ h2)
  refine ⟨L, hs, hreal, ?_⟩
  change (_ ∧ _)
  rw [hs]
  exact ⟨producedStages'_projection_model a p hK hS₀ h2,
    producedStages'_trace_transport a p hK hS₀ h2⟩

/-- Kind: PROVED. The support-change realized assembler on the strengthened
stage choice, with the requested projection link and original local-cup
trace identities preserved. Its arithmetic assumptions are unchanged;
tex 3483–3498, 4385–4451, 4859–4873, 4976–5135. -/
theorem assemble_from_support_change_realized' (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R) (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) U hU Cn hW,
        L.stages = producedStages' (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6)
          p hK hS₀ h2 ∧ L.Realized ∧ L.StageLinks := by
  let T := residualSupport_six_of_stage_dimensions F R p h788 hK hS₀ h2 P
    (fun i _ => (stage i).localDimensions)
  obtain ⟨L, hs, hreal, hlinks⟩ :=
    assemble_inner_limit_realized' p hK hS₀ h2 ⟨oldFlat, T, stage⟩ U hU Cn hW
  exact ⟨T, L, hs, hreal, hlinks⟩

end LinkedRealizedAssembly

section ResidueTraceIdentification

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F} {i : ℕ} [NeZero i]
  (S : StageArithmeticInput F O i)

/-- Kind: GLUE. The remaining original-cochain identification with an
independent residue-arithmetic presentation. These three fields compare the
original compact trace on the exact included cochains with actual transported
cups, not with determinant tables. The coefficient, conjugation, representative
and scalar-trace dictionaries in this identification remain open;
tex 4385–4451, 4860–4863, 5027–5043. -/
structure OriginalResidueTraceIdentification (B : LinkedSplitStage S)
    (Y : StageArithmeticData i) : Prop where
  /-- Kind: GLUE. OPEN zero/two original trace identification;
  tex 4385–4451, 4860–4863. -/
  identification02 : ∀ x y : Fin 2 → Acoef i,
    originalCupTrace S B.originalTrace B.localRetract 0 2 rfl x y = Y.cup02 x y
  /-- Kind: GLUE. OPEN one/one original trace identification;
  tex 4385–4451, 4860–4863. -/
  identification11 : ∀ x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i),
    originalCupTrace S B.originalTrace B.localRetract 1 1 rfl x y = Y.cup11 x y
  /-- Kind: GLUE. OPEN two/zero original trace identification;
  tex 4385–4451, 4860–4863. -/
  identification20 : ∀ x y : Fin 2 → Acoef i,
    originalCupTrace S B.originalTrace B.localRetract 2 0 rfl x y = Y.cup20 x y

/-- Kind: definition. The strengthened output with the remaining original
residue-cochain identification stored explicitly. Its three split trace
identities are derived from that identification and the original transports;
tex 4385–4451, 4860–4863, 5027–5043. -/
structure ResidueLinkedSplitStage (Y : StageArithmeticData i) where
  /-- Kind: definition. The same strengthened split-stage witnesses;
  tex 4385–4451, 4859–4873. -/
  links : LinkedSplitStage S
  /-- Kind: GLUE. OPEN arithmetic original trace identification, on the
  same retained trace and normalized inclusion; tex 4385–4451, 4860–4863. -/
  original_identification : OriginalResidueTraceIdentification S links Y
  /-- Kind: PROVED. The zero/two split trace identity consumed by the
  original residue-arithmetic reduction; tex 4385–4451, 4860–4863. -/
  htrace02 : ∀ x y : Fin 2 → Acoef i,
    links.toSplitStage.trace (0, links.toSplitStage.pairing.cupL.P 0 2 2 rfl x y) = Y.cup02 x y
  /-- Kind: PROVED. The one/one split trace identity consumed by the
  original residue-arithmetic reduction; tex 4385–4451, 4860–4863. -/
  htrace11 : ∀ x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i),
    links.toSplitStage.trace (0, links.toSplitStage.pairing.cupL.P 1 1 2 rfl x y) = Y.cup11 x y
  /-- Kind: PROVED. The two/zero split trace identity consumed by the
  original residue-arithmetic reduction; tex 4385–4451, 4860–4863. -/
  htrace20 : ∀ x y : Fin 2 → Acoef i,
    links.toSplitStage.trace (0, links.toSplitStage.pairing.cupL.P 2 0 2 rfl x y) = Y.cup20 x y

/-- Kind: PROVED. Package the exact residue-consumer trace identities from
an explicitly supplied original-cochain identification. This constructor does
not claim to prove the identification itself;
tex 4385–4451, 4860–4863, 5027–5043. -/
def LinkedSplitStage.withResidueIdentification (B : LinkedSplitStage S)
    (Y : StageArithmeticData i) (h : OriginalResidueTraceIdentification S B Y) :
    ResidueLinkedSplitStage S Y :=
  ⟨B, h, fun x y => (B.htrace02 x y).trans (h.identification02 x y),
    fun x y => (B.htrace11 x y).trans (h.identification11 x y),
    fun x y => (B.htrace20 x y).trans (h.identification20 x y)⟩

end ResidueTraceIdentification

section MatchedStageChoice

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}

/-- Kind: definition. Preserve the chosen strengthened stage and the open
original identification in a residue-linked record. There is no second choice
of projection, compact trace or inclusion; tex 4385–4451, 4860–4863. -/
def producedResidueStageLinks' (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i))
    (i : ℕ) [NeZero i] : ResidueLinkedSplitStage (a.stage i) (Y i) :=
  LinkedSplitStage.withResidueIdentification (a.stage i)
    (producedStageLinks' a p hK hS₀ h2 i) (Y i) (h i)

/-- Kind: definition. Forget the residue-linked record only after its
original identification and all three split trace identities have been fixed;
tex 4385–4451, 4860–4863. -/
def producedResidueStages' (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i)) :
    ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)
  | 0 => zeroSplitStage F _ _
  | i + 1 => (producedResidueStageLinks' a p hK hS₀ h2 Y h (i + 1)).links.toSplitStage

/-- Kind: PROVED. Adding the remaining arithmetic identification does not
change any chosen split stage or its projection and trace;
tex 4385–4451, 4860–4863. -/
theorem producedResidueStages'_eq (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i)) :
    producedResidueStages' a p hK hS₀ h2 Y h = producedStages' a p hK hS₀ h2 := by
  funext i
  cases i <;> rfl

/-- Kind: PROVED. The exact zero/two residue-consumer hypothesis follows
from the remaining original identification for the chosen witnesses;
tex 4385–4451, 4860–4863. -/
theorem producedStages'_htrace02_of_identification (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i)) :
    ∀ i [NeZero i] (x y : Fin 2 → Acoef i),
      (producedStages' a p hK hS₀ h2 i).trace
        (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 0 2 2 rfl x y) =
        (Y i).cup02 x y := by
  intro i _ x y
  exact (producedStages'_htrace02 a p hK hS₀ h2 i x y).trans ((h i).identification02 x y)

/-- Kind: PROVED. The exact one/one residue-consumer hypothesis follows
from the same original identification and chosen trace;
tex 4385–4451, 4860–4863. -/
theorem producedStages'_htrace11_of_identification (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i)) :
    ∀ i [NeZero i] (x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i)),
      (producedStages' a p hK hS₀ h2 i).trace
        (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 1 1 2 rfl x y) =
        (Y i).cup11 x y := by
  intro i _ x y
  exact (producedStages'_htrace11 a p hK hS₀ h2 i x y).trans ((h i).identification11 x y)

/-- Kind: PROVED. The exact two/zero residue-consumer hypothesis follows
from the same original identification and chosen inclusion;
tex 4385–4451, 4860–4863. -/
theorem producedStages'_htrace20_of_identification (a : ArithmeticInputs F O R width)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i)) :
    ∀ i [NeZero i] (x y : Fin 2 → Acoef i),
      (producedStages' a p hK hS₀ h2 i).trace
        (0, (producedStages' a p hK hS₀ h2 i).pairing.cupL.P 2 0 2 rfl x y) =
        (Y i).cup20 x y := by
  intro i _ x y
  exact (producedStages'_htrace20 a p hK hS₀ h2 i x y).trans ((h i).identification20 x y)

end MatchedStageChoice

section ResidueLinkedAssembly

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}
  {a : ArithmeticInputs F O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ Filter.cofinite} {Cn : ActualConj K S₀}
  {hW : W.map (Cn.κ : K →+* K) = W}

/-- Kind: definition. The three exact residue-consumer trace hypotheses
for a prescribed split-stage family. The predicate keeps the family's cup
targets bundled during transport; tex 4385–4451, 4860–4863, 5027–5043. -/
def StageResidueTraceLinks (a : ArithmeticInputs F O R width)
    (s : ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i))
    (Y : ∀ i [NeZero i], StageArithmeticData i) : Prop :=
  (∀ i [NeZero i] (x y : Fin 2 → Acoef i),
    (s i).trace (0, (s i).pairing.cupL.P 0 2 2 rfl x y) = (Y i).cup02 x y) ∧
  (∀ i [NeZero i] (x y : (Fin 2 → Acoef i) × (Fin 2 → Acoef i)),
    (s i).trace (0, (s i).pairing.cupL.P 1 1 2 rfl x y) = (Y i).cup11 x y) ∧
  (∀ i [NeZero i] (x y : Fin 2 → Acoef i),
    (s i).trace (0, (s i).pairing.cupL.P 2 0 2 rfl x y) = (Y i).cup20 x y)

/-- Kind: definition. The three residue-consumer trace hypotheses on this
assembled limit's own stages, with no determinant table assumed;
tex 4385–4451, 4860–4863, 5027–5043. -/
def AssembledLimit.ResidueTraceLinks (L : AssembledLimit a U hU Cn hW)
    (Y : ∀ i [NeZero i], StageArithmeticData i) : Prop :=
  StageResidueTraceLinks a L.stages Y

/-- Kind: PROVED. The realized linked assembler with the explicitly open
original-cochain identifications. These identifications are carried in
residue-linked stage records and supply all three consumer trace hypotheses
on the same retained diagram; tex 4385–4451, 4860–4863, 5027–5043. -/
theorem assemble_inner_limit_residue_realized' (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (a.stage i)
      (producedStageLinks' a p hK hS₀ h2 i) (Y i))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ L : AssembledLimit a U hU Cn hW,
      L.stages = producedStages' a p hK hS₀ h2 ∧ L.Realized ∧
        L.StageLinks ∧ L.ResidueTraceLinks Y := by
  obtain ⟨L, hs, hreal, hlinks⟩ := assemble_inner_limit_realized' p hK hS₀ h2 a U hU Cn hW
  refine ⟨L, hs, hreal, hlinks, ?_⟩
  change StageResidueTraceLinks a L.stages Y
  rw [hs]
  exact ⟨producedStages'_htrace02_of_identification a p hK hS₀ h2 Y h,
    producedStages'_htrace11_of_identification a p hK hS₀ h2 Y h,
    producedStages'_htrace20_of_identification a p hK hS₀ h2 Y h⟩

/-- Kind: PROVED. Support-change assembly with the independent residue
presentation. The only added hypotheses identify the original compact trace
cups of the selected normalized retractions with the actual transported local
cups. Those are named open cochain identifications, not residue formulae;
tex 3483–3498, 4385–4451, 4860–4863, 4976–5135. -/
theorem assemble_from_support_change_residue_realized' (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R) (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (Y : ∀ i [NeZero i], StageArithmeticData i)
    (h : ∀ i [NeZero i], OriginalResidueTraceIdentification (stage i)
      ((stage i).chosen_links p hK hS₀ h2) (Y i))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) U hU Cn hW,
        L.stages = producedStages' (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6)
          p hK hS₀ h2 ∧ L.Realized ∧ L.StageLinks ∧ L.ResidueTraceLinks Y := by
  let T := residualSupport_six_of_stage_dimensions F R p h788 hK hS₀ h2 P
    (fun i _ => (stage i).localDimensions)
  obtain ⟨L, hs, hreal, hlinks, htrace⟩ := assemble_inner_limit_residue_realized'
    p hK hS₀ h2 (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) Y h U hU Cn hW
  exact ⟨T, L, hs, hreal, hlinks, htrace⟩

end ResidueLinkedAssembly

end ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange
