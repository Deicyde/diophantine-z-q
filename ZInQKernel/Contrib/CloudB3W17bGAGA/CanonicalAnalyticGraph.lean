import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalOriginalPoints
import ZInQKernel.Contrib.CloudB3W17GAGA.Graph
import ZInQKernel.Contrib.CloudB3W17Uniformization.Uniformization
import ZInQKernel.Contrib.CloudB3W17ProperCompact.NativeCompact
import ZInQKernel.Contrib.CloudB3W17Lattice.CompactQuotient

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open ZInQ.Contrib.CloudB3W17GAGA

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGAGA

local instance cptsIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

local instance cptsTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X

local instance cptsChartedSpace (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    ChartedSpace (Fin n → ℂ) (APts A) := CloudB3W17Hodge.chartedSpace A.X n

local instance cptsManifold (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A) := CloudB3W17Hodge.isManifold_cpt A.X n

/-- Compactness in the unchanged canonical topology on the original complex points. -/
theorem compactSpace_canonical (A : AbVar ℂ) : CompactSpace (APts A) := by
  let : CompactSpace (ComplexPoint A.X) :=
    W17ProperCompact.compactSpace_complexPoint_of_isIntegral_isProper A.X
  exact (cptModelHomeomorph A).symm.compactSpace

/-- Every original strong uniformization of a complex abelian variety already has a full lattice. -/
theorem isZLattice_of_strongUnif (A : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) : IsZLattice ℝ Λ := by
  let : CompactSpace (APts A) := compactSpace_canonical A
  obtain ⟨e, -, -⟩ := strongUnif_canonical_diffeomorph A φ hφ
  let : CompactSpace (BPAnalytic.Torus Λ) := e.toHomeomorph.symm.compactSpace
  exact CloudB3W17Lattice.isZLattice_of_compactSpace_quotient Λ

/-- The point-level descent is complex analytic in the actual canonical atlases.
The target uniformization is obtained from the proved uniformization theorem, not assumed. -/
theorem contMDiff_pointDescentHom_canonical (A B : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ)
    {ψ : (Fin g → ℂ) → APts B} (hψ : IsAnalyticHom (RingHom.id ℂ) ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (pointDescentHom φ hψ hΛ) := by
  obtain ⟨gB, ΛB, hdB, -, φB, hφB⟩ := ZInQ.HomLattice.strong_id_of_leaf
    CloudB3W17Uniformization.uniformizationLeafAll B
  let : DiscreteTopology ΛB := hdB
  obtain ⟨eA, -, heAi⟩ := strongUnif_canonical_diffeomorph A φ hφ
  obtain ⟨eB, heB, -⟩ := strongUnif_canonical_diffeomorph B φB hφB
  let T := targetTorusHom φB hψ hΛ
  have hc := eB.contMDiff.comp ((contMDiff_targetTorusHom φB hφB hψ hΛ).comp eA.symm.contMDiff)
  change ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
    𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (fun P => eB (T (eA.symm P))) at hc
  have heq : (fun P => eB (T (eA.symm P))) = (pointDescentHom φ hψ hΛ : APts A → APts B) := by
    funext P
    rw [heB (T (eA.symm P)), heAi P]
    change Additive.toMul (φB (φB.symm (descendHom hψ hΛ (phiInv φ P)))) =
      Additive.toMul (descendHom hψ hΛ (phiInv φ P))
    rw [AddEquiv.apply_symm_apply]
  exact heq ▸ hc

/-- Unique complex-analytic group descent, with precisely the original three hypotheses. -/
theorem existsUnique_analytic_descent_canonical (A B : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ)
    {ψ : (Fin g → ℂ) → APts B} (hψ : IsAnalyticHom (RingHom.id ℂ) ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃! F : APts A →* APts B,
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F ∧
        ∀ z, F (phiPts φ (BPAnalytic.proj Λ z)) = ψ z := by
  refine ⟨pointDescentHom φ hψ hΛ,
    ⟨contMDiff_pointDescentHom_canonical A B φ hφ hψ hΛ, pointDescentHom_spec φ hψ hΛ⟩, ?_⟩
  intro F hF
  exact pointDescentHom_unique φ hψ hΛ F hF.2

/-- The canonical topology is Hausdorff; the target presentation is obtained from the proved theorem. -/
theorem t2Space_canonical (A : AbVar ℂ) : T2Space (APts A) := by
  obtain ⟨g, Λ, hd, -, φ, hφ⟩ := ZInQ.HomLattice.strong_id_of_leaf
    CloudB3W17Uniformization.uniformizationLeafAll A
  let : DiscreteTopology Λ := hd
  obtain ⟨e, -, -⟩ := strongUnif_canonical_diffeomorph A φ hφ
  have : T1Space (BPAnalytic.Torus Λ) :=
    ChartedSpace.t1Space (H := Fin g → ℂ) (M := BPAnalytic.Torus Λ)
  exact e.toHomeomorph.t2Space

/-- The ordinary graph subgroup on the original complex-point carriers. -/
def graphSubgroup {A B : AbVar ℂ} (F : APts A →* APts B) : Subgroup (APts A × APts B) where
  carrier := {p | F p.1 = p.2}
  one_mem' := map_one F
  mul_mem' := by
    intro p q hp hq
    change F (p.1 * q.1) = p.2 * q.2
    rw [map_mul, hp, hq]
  inv_mem' := by
    intro p hp
    change F p.1⁻¹ = p.2⁻¹
    rw [map_inv, hp]

/-- The canonical point graph is closed. This does not assert an algebraic subscheme. -/
def closedGraph {A B : AbVar ℂ} (F : APts A →* APts B) (hF : Continuous F) :
    ClosedSubgroup (APts A × APts B) where
  toSubgroup := graphSubgroup F
  isClosed' := by
    have : T2Space (APts B) := t2Space_canonical B
    exact isClosed_eq (hF.comp continuous_fst) continuous_snd

@[simp]
theorem mem_closedGraph {A B : AbVar ℂ} (F : APts A →* APts B) (hF : Continuous F)
    (p : APts A × APts B) : p ∈ closedGraph F hF ↔ F p.1 = p.2 := Iff.rfl

/-- The image of the graph parametrization is its ordinary subgroup carrier. -/
theorem range_graphMap {A B : AbVar ℂ} (F : APts A →* APts B) :
    Set.range (fun P => (P, F P)) = (graphSubgroup F : Set (APts A × APts B)) := by
  ext p
  constructor
  · rintro ⟨P, rfl⟩
    rfl
  · intro hp
    exact ⟨p.1, Prod.ext rfl hp⟩

/-- The graph is homeomorphic to the original source, by its first projection. -/
def graphHomeomorph {A B : AbVar ℂ} (F : APts A →* APts B) (hF : Continuous F) :
    APts A ≃ₜ closedGraph F hF where
  toFun P := ⟨(P, F P), rfl⟩
  invFun p := p.1.1
  left_inv P := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.2
  continuous_toFun := (continuous_id.prodMk hF).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The canonical graph is compact, using properness of the actual source abelian variety. -/
theorem isCompact_closedGraph {A B : AbVar ℂ} (F : APts A →* APts B) (hF : Continuous F) :
    IsCompact (closedGraph F hF : Set (APts A × APts B)) := by
  let : CompactSpace (APts A) := compactSpace_canonical A
  change IsCompact (graphSubgroup F : Set (APts A × APts B))
  rw [← range_graphMap F]
  simpa only [Set.image_univ, id_eq] using
    (isCompact_univ : IsCompact (Set.univ : Set (APts A))).image (continuous_id.prodMk hF)

/-- First projection supplies a continuous linear left inverse to the complex graph differential. -/
theorem graph_mfderiv_leftInverse {A B : AbVar ℂ} (F : APts A →* APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F) (P : APts A) :
    Function.LeftInverse
      (mfderiv (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
          𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ))
        𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        (Prod.fst : APts A × APts B → APts A) (P, F P))
      (mfderiv 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
          𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) (fun Q => (Q, F Q)) P) := by
  have hg : MDifferentiableAt 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) (fun Q => (Q, F Q)) P :=
    mdifferentiableAt_id.prodMk (hF P)
  have hp : MDifferentiableAt (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ))
      𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      (Prod.fst : APts A × APts B → APts A) (P, F P) := mdifferentiableAt_fst
  have heq : (Prod.fst : APts A × APts B → APts A) ∘ (fun Q => (Q, F Q)) = id := rfl
  have hc := mfderiv_comp P hp hg
  rw [heq, mfderiv_id] at hc
  intro v
  exact (congrArg (fun L => L v) hc).symm

/-- The canonical graph parametrization is an immersion in the sense of its complex differential. -/
theorem isDiffImmersionAt_graphMap {A B : AbVar ℂ} (F : APts A →* APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F) (P : APts A) :
    IsDiffImmersionAt 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) (fun Q => (Q, F Q)) P := by
  exact ⟨mfderiv (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ))
      𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      (Prod.fst : APts A × APts B → APts A) (P, F P), graph_mfderiv_leftInverse F hF P⟩

/-- The graph has genuine finite complex-analytic equations in regular target coordinates.
These are analytic differences, not algebraic pullbacks along an already constructed scheme map. -/
theorem graph_locally_zero_coordinate_differences {A B : AbVar ℂ} (F : APts A →* APts B)
    (hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F) (P : APts A) :
    ∃ (N : Set (APts A × APts B)) (U : B.X.left.Opens)
      (s : Fin (TopologicalSpace.dim B.X.left) → Γ(B.X.left, U)),
      IsOpen N ∧ (P, F P) ∈ N ∧
      (∀ i, ContMDiffOn (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
          𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) 𝓘(ℂ, ℂ) ω
        (fun q => ZInQ.LeafPush2.cEvalAt q.2 U (s i) -
          ZInQ.LeafPush2.cEvalAt (F q.1) U (s i)) N) ∧
      ∀ q ∈ N, F q.1 = q.2 ↔ ∀ i,
        ZInQ.LeafPush2.cEvalAt q.2 U (s i) - ZInQ.LeafPush2.cEvalAt (F q.1) U (s i) = 0 := by
  obtain ⟨U, s, hU, hloc⟩ := canonical_cpts_coords B (TopologicalSpace.dim B.X.left) (F P)
  obtain ⟨e, he, heq⟩ := hloc
  let W : Set (APts B) := e.source ∩ pointDom B U
  let N : Set (APts A × APts B) := {q | F q.1 ∈ W ∧ q.2 ∈ W}
  have hW : IsOpen W := e.open_source.inter (canonical_isOpen_pointDom B U)
  have hN : IsOpen N :=
    (hW.preimage (hF.continuous.comp continuous_fst)).inter (hW.preimage continuous_snd)
  refine ⟨N, U, s, hN, ⟨⟨he, hU⟩, ⟨he, hU⟩⟩, ?_, ?_⟩
  · intro i
    have hs := canonical_cpts_holo B (TopologicalSpace.dim B.X.left) U (s i)
    have h₂ : ContMDiffOn (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) 𝓘(ℂ, ℂ) ω
        (fun q : APts A × APts B => ZInQ.LeafPush2.cEvalAt q.2 U (s i)) N :=
      hs.comp contMDiff_snd.contMDiffOn (fun (q : APts A × APts B) (hq : q ∈ N) => hq.2.2)
    have h₁ : ContMDiffOn (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) 𝓘(ℂ, ℂ) ω
        (fun q : APts A × APts B => ZInQ.LeafPush2.cEvalAt (F q.1) U (s i)) N :=
      hs.comp (hF.comp contMDiff_fst).contMDiffOn
        (fun (q : APts A × APts B) (hq : q ∈ N) => hq.1.2)
    exact h₂.sub h₁
  · intro q hq
    constructor
    · intro hg i
      rw [hg]
      exact sub_self _
    · intro hz
      have hc : (fun R i => ZInQ.LeafPush2.cEvalAt R U (s i)) q.2 =
          (fun R i => ZInQ.LeafPush2.cEvalAt R U (s i)) (F q.1) :=
        funext fun i => sub_eq_zero.mp (hz i)
      have hec : e (F q.1) = e q.2 :=
        (heq hq.1.1).symm.trans (hc.symm.trans (heq hq.2.1))
      exact e.toPartialEquiv.injOn hq.1.1 hq.2.1 hec

/-- The graph parametrization is a closed topological embedding on the original carriers. -/
theorem isClosedEmbedding_graphMap {A B : AbVar ℂ} (F : APts A →* APts B) (hF : Continuous F) :
    Topology.IsClosedEmbedding (fun P : APts A => (P, F P)) := by
  have hemb : Topology.IsEmbedding (fun P : APts A => (P, F P)) :=
    (show Function.LeftInverse (Prod.fst : APts A × APts B → APts A)
      (fun P : APts A => (P, F P)) from fun _ => rfl).isEmbedding
      continuous_fst (continuous_id.prodMk hF)
  refine ⟨hemb, ?_⟩
  rw [range_graphMap F]
  exact (closedGraph F hF).isClosed'

/-- Closed, compact and analytically parametrized original-point graph from exactly the original inputs.
No algebraic graph, scheme morphism, projectivity or target-uniformization premise is supplied. -/
theorem exists_closed_compact_analytic_graph_canonical (A B : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ)
    {ψ : (Fin g → ℂ) → APts B} (hψ : IsAnalyticHom (RingHom.id ℂ) ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃ F : APts A →* APts B,
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F ∧
      (∀ z, F (phiPts φ (BPAnalytic.proj Λ z)) = ψ z) ∧
      ∃ H : ClosedSubgroup (APts A × APts B),
        (∀ p, p ∈ H ↔ F p.1 = p.2) ∧ IsCompact (H : Set (APts A × APts B)) ∧
        Nonempty (APts A ≃ₜ H) ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
          (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
            𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) ω (fun P => (P, F P)) ∧
        Topology.IsClosedEmbedding (fun P : APts A => (P, F P)) ∧
        ∀ P, IsDiffImmersionAt 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
          (𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ).prod
            𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ)) (fun Q => (Q, F Q)) P := by
  let F := pointDescentHom φ hψ hΛ
  have hF := contMDiff_pointDescentHom_canonical A B φ hφ hψ hΛ
  have hc : Continuous F := hF.continuous
  refine ⟨F, hF, pointDescentHom_spec φ hψ hΛ, closedGraph F hc,
    mem_closedGraph F hc, isCompact_closedGraph F hc, ⟨graphHomeomorph F hc⟩,
    contMDiff_id.prodMk hF, isClosedEmbedding_graphMap F hc, ?_⟩
  intro P
  exact isDiffImmersionAt_graphMap F (fun Q => (hF Q).mdifferentiableAt (by simp)) P

end ZInQ.Contrib.CloudB3W17bGAGA

