import ZInQKernel.Contrib.CloudB3W17GAGA.Descent
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Geometry.Manifold.ImmersionDiff

/-!
# The descended analytic homomorphism in a supplied target torus

W17 H105 preparatory supplier. A supplied strong uniformization of B makes
the descent a continuous (indeed analytic) map between the two tori. Its
graph is a closed additive subgroup, is homeomorphic to the source by its
first projection, and is compact when the source quotient is compact.

The target linear lift and BPAnalytic's global projection descent are REUSED,
not re-proved. Source compactness/full-lattice existence is a separate input.
None of these facts algebraizes the graph or proves `GAGAMorphism`.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open BPAnalytic (Torus proj)

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

variable {K : Type} [Field K] {B : AbVar K} {σ : K →+* ℂ} {g h : ℕ}
variable {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
variable {ΛB : Submodule ℤ (Fin h → ℂ)} [DiscreteTopology ΛB]
variable {ψ : (Fin g → ℂ) → CPts B σ}

/-- The unique quotient descent expressed in a supplied presentation of B. -/
def targetTorusHom (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) : Torus Λ →+ Torus ΛB :=
  φB.symm.toAddMonoidHom.comp (descendHom hψ hΛ)

omit [DiscreteTopology Λ] [DiscreteTopology ΛB] in
@[simp]
theorem targetTorusHom_proj (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) (z : Fin g → ℂ) :
    targetTorusHom φB hψ hΛ (proj Λ z) = φB.symm (Additive.ofMul (ψ z)) := rfl

omit [DiscreteTopology Λ] [DiscreteTopology ΛB] in
/-- Continuity is the quotient-map consequence of the existing strong-target comparison. -/
theorem continuous_targetTorusHom (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hφB : IsStrongUnif B σ ΛB φB) (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) : Continuous (targetTorusHom φB hψ hΛ) := by
  apply (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff.mpr
  change Continuous (fun z => φB.symm (Additive.ofMul (ψ z)))
  exact ZInQ.HomLattice.continuous_symm_comp_strong hφB hψ

/-- The supplied strong target makes this particular homomorphism analytic.
This uses the already proved complex-linear lift; it does NOT assert a general
multivariable DifferentiableOn-to-analytic theorem. -/
theorem contMDiff_targetTorusHom (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hφB : IsStrongUnif B σ ΛB φB) (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin h → ℂ) ω (targetTorusHom φB hψ hΛ) := by
  apply BPAnalytic.contMDiff_of_comp_proj Λ
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong hφB hψ
  have heq : (targetTorusHom φB hψ hΛ) ∘ proj Λ = proj ΛB ∘ D := by
    funext z
    change φB.symm (Additive.ofMul (ψ z)) = proj ΛB (D z)
    apply φB.injective
    apply Additive.toMul.injective
    rw [AddEquiv.apply_symm_apply, hD z]
    rfl
  rw [heq]
  exact (BPAnalytic.contMDiff_proj ΛB).comp (contMDiff_iff_contDiff.mpr D.contDiff)

/-- The ordinary graph subgroup, formed from the supplied torus homomorphism. -/
def graphAddSubgroup (F : Torus Λ →+ Torus ΛB) : AddSubgroup (Torus Λ × Torus ΛB) where
  carrier := {p | F p.1 = p.2}
  zero_mem' := map_zero F
  add_mem' := by
    intro p q hp hq
    change F (p.1 + q.1) = p.2 + q.2
    rw [map_add, hp, hq]
  neg_mem' := by
    intro p hp
    change F (-p.1) = -p.2
    rw [map_neg, hp]

omit [DiscreteTopology Λ] [DiscreteTopology ΛB] in
@[simp]
theorem mem_graphAddSubgroup (F : Torus Λ →+ Torus ΛB) (p : Torus Λ × Torus ΛB) :
    p ∈ graphAddSubgroup F ↔ F p.1 = p.2 := Iff.rfl

/-- The closed graph in the genuine target quotient topology. -/
def closedGraph (F : Torus Λ →+ Torus ΛB) (hF : Continuous F) :
    ClosedAddSubgroup (Torus Λ × Torus ΛB) where
  toAddSubgroup := graphAddSubgroup F
  isClosed' := by
    have : T1Space (Torus ΛB) := ChartedSpace.t1Space (H := Fin h → ℂ) (M := Torus ΛB)
    change IsClosed {p : Torus Λ × Torus ΛB | F p.1 = p.2}
    exact isClosed_eq (hF.comp continuous_fst) continuous_snd

omit [DiscreteTopology Λ] in
@[simp]
theorem mem_closedGraph (F : Torus Λ →+ Torus ΛB) (hF : Continuous F)
    (p : Torus Λ × Torus ΛB) : p ∈ closedGraph F hF ↔ F p.1 = p.2 := Iff.rfl

omit [DiscreteTopology Λ] [DiscreteTopology ΛB] in
/-- The parametrization of the graph has image exactly its carrier. -/
theorem range_graphMap (F : Torus Λ →+ Torus ΛB) :
    Set.range (fun q => (q, F q)) = (graphAddSubgroup F : Set (Torus Λ × Torus ΛB)) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · intro hp
    exact ⟨p.1, Prod.ext rfl hp⟩

/-- The first projection identifies the graph homeomorphically with the source.
This is a topological statement, not an algebraic projection-isomorphism claim. -/
def graphHomeomorph (F : Torus Λ →+ Torus ΛB) (hF : Continuous F) :
    Torus Λ ≃ₜ closedGraph F hF where
  toFun q := ⟨(q, F q), rfl⟩
  invFun p := p.1.1
  left_inv q := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.2
  continuous_toFun := (continuous_id.prodMk hF).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

omit [DiscreteTopology Λ] in
/-- Compactness of the graph requires only compactness of its source, not of the target. -/
theorem isCompact_closedGraph [CompactSpace (Torus Λ)]
    (F : Torus Λ →+ Torus ΛB) (hF : Continuous F) :
    IsCompact (closedGraph F hF : Set (Torus Λ × Torus ΛB)) := by
  change IsCompact (graphAddSubgroup F : Set (Torus Λ × Torus ΛB))
  rw [← range_graphMap F]
  simpa only [Set.image_univ, id_eq] using
    (isCompact_univ : IsCompact (Set.univ : Set (Torus Λ))).image (continuous_id.prodMk hF)

/-- The graph parametrization is complex analytic when the target presentation is supplied. -/
theorem contMDiff_targetTorusGraph (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hφB : IsStrongUnif B σ ΛB φB) (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ContMDiff 𝓘(ℂ, Fin g → ℂ)
      (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ)) ω
      (fun q => (q, targetTorusHom φB hψ hΛ q)) :=
  contMDiff_id.prodMk (contMDiff_targetTorusHom φB hφB hψ hΛ)

/-- The first graph projection supplies a continuous linear left inverse to its derivative. -/
theorem graph_mfderiv_leftInverse (F : Torus Λ →+ Torus ΛB)
    (hF : MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin h → ℂ) F) (q : Torus Λ) :
    Function.LeftInverse
      (mfderiv (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ)) 𝓘(ℂ, Fin g → ℂ)
        (Prod.fst : Torus Λ × Torus ΛB → Torus Λ) (q, F q))
      (mfderiv 𝓘(ℂ, Fin g → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ))
        (fun p => (p, F p)) q) := by
  have hg : MDifferentiableAt 𝓘(ℂ, Fin g → ℂ)
      (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ)) (fun p => (p, F p)) q :=
    mdifferentiableAt_id.prodMk (hF q)
  have hp : MDifferentiableAt (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ))
      𝓘(ℂ, Fin g → ℂ) (Prod.fst : Torus Λ × Torus ΛB → Torus Λ) (q, F q) :=
    mdifferentiableAt_fst
  have heq : (Prod.fst : Torus Λ × Torus ΛB → Torus Λ) ∘ (fun p => (p, F p)) = id := rfl
  have hc := mfderiv_comp q hp hg
  rw [heq, mfderiv_id] at hc
  intro v
  exact (congrArg (fun L => L v) hc).symm

/-- The graph is a differential immersion, not merely an injective continuous parametrization. -/
theorem isDiffImmersionAt_graphMap (F : Torus Λ →+ Torus ΛB)
    (hF : MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin h → ℂ) F) (q : Torus Λ) :
    IsDiffImmersionAt 𝓘(ℂ, Fin g → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ))
      (fun p => (p, F p)) q := by
  exact ⟨mfderiv (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ)) 𝓘(ℂ, Fin g → ℂ)
    (Prod.fst : Torus Λ × Torus ΛB → Torus Λ) (q, F q), graph_mfderiv_leftInverse F hF q⟩

/-- The supplied-target graph has injective complex differential at every point. -/
theorem isDiffImmersionAt_targetTorusGraph (φB : Torus ΛB ≃+ Additive (CPts B σ))
    (hφB : IsStrongUnif B σ ΛB φB) (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) (q : Torus Λ) :
    IsDiffImmersionAt 𝓘(ℂ, Fin g → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ))
      (fun p => (p, targetTorusHom φB hψ hΛ p)) q :=
  isDiffImmersionAt_graphMap (targetTorusHom φB hψ hΛ)
    (fun p => (contMDiff_targetTorusHom φB hφB hψ hΛ p).mdifferentiableAt (by simp)) q

/-- Closed and compact analytic graph package under a supplied strong target.
Algebraicity is deliberately absent from the conclusion and from the premises. -/
theorem exists_closed_compact_targetTorusGraph [CompactSpace (Torus Λ)]
    (φB : Torus ΛB ≃+ Additive (CPts B σ)) (hφB : IsStrongUnif B σ ΛB φB)
    (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃ H : ClosedAddSubgroup (Torus Λ × Torus ΛB),
      (∀ p, p ∈ H ↔ φB.symm (descendHom hψ hΛ p.1) = p.2) ∧
      IsCompact (H : Set (Torus Λ × Torus ΛB)) ∧
      Nonempty (Torus Λ ≃ₜ H) ∧
      ContMDiff 𝓘(ℂ, Fin g → ℂ)
        (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ)) ω
        (fun q => (q, targetTorusHom φB hψ hΛ q)) ∧
      ∀ q, IsDiffImmersionAt 𝓘(ℂ, Fin g → ℂ)
        (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin h → ℂ))
        (fun p => (p, targetTorusHom φB hψ hΛ p)) q := by
  let F := targetTorusHom φB hψ hΛ
  have hF : Continuous F := continuous_targetTorusHom φB hφB hψ hΛ
  refine ⟨closedGraph F hF, ?_, isCompact_closedGraph F hF,
    ⟨graphHomeomorph F hF⟩, contMDiff_targetTorusGraph φB hφB hψ hΛ,
    isDiffImmersionAt_targetTorusGraph φB hφB hψ hΛ⟩
  intro p
  rfl

end ZInQ.Contrib.CloudB3W17GAGA
