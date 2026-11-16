import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.CloudB3W17ZeroDim.Basic

/-!
# GAGA's exact conclusion for zero-dimensional sources

If the source abelian variety has dimension at most zero, its complex point group
is a singleton. A quotient presentation of that group forces every vector into
the lattice. Hence every map killing the lattice is the constant identity map,
and the algebraic zero morphism realizes it.

The conclusion here is exactly the realization conclusion of `GAGAMorphism` for
this class of sources, including arbitrary `g`, `Λ`, and quotient isomorphism.
Neither analytification nor an algebraicity input is assumed. This does NOT prove
the universally quantified OneProof field `gagaMorphism`.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry Limits MonObj PkgI3
open ZInQ.LeafPush2 (CPts)

noncomputable section

namespace CloudB3W17.ZeroDim

/-- The realization conclusion of GAGA for any source with a singleton complex point group. -/
theorem gaga_realization_of_subsingleton (A B : AbVar ℂ)
    [Subsingleton (CPts A (RingHom.id ℂ))] (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ)))
    (ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ)) (hker : ∀ z ∈ Λ, ψ z = 1) :
    ∃ f : A.X ⟶ B.X, ∀ z,
      ψ z = Additive.toMul (φ (BPAnalytic.proj Λ z)) ≫ f := by
  refine ⟨(1 : A.X ⟶ B.X), fun z => ?_⟩
  have hz : BPAnalytic.proj Λ z = 0 := φ.injective (Subsingleton.elim _ _)
  have hmem : z ∈ Λ := (QuotientAddGroup.eq_zero_iff z).mp hz
  rw [hker z hmem]
  exact (MonObj.comp_one _).symm

/-- GAGA's exact realization conclusion for a zero-dimensional complex abelian variety. -/
theorem gaga_realization_of_dim_le_zero (A B : AbVar ℂ) (hA : A.dim ≤ 0) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ)))
    (ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ)) (hker : ∀ z ∈ Λ, ψ z = 1) :
    ∃ f : A.X ⟶ B.X, ∀ z,
      ψ z = Additive.toMul (φ (BPAnalytic.proj Λ z)) ≫ f := by
  have : Subsingleton (CPts A (RingHom.id ℂ)) := subsingleton_pts_of_dim_le_zero A hA
  exact gaga_realization_of_subsingleton A B g Λ φ ψ hker

/-- The literal GAGA binders and conclusion hold for every zero-dimensional source. -/
theorem gagaMorphism_zero_dim (A B : AbVar ℂ) (hA : A.dim ≤ 0) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ)))
    (_hφ : ZInQ.HomLattice.IsStrongUnif A (RingHom.id ℂ) Λ φ)
    (ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ))
    (_hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ)
    (hker : ∀ z ∈ Λ, ψ z = 1) :
    ∃ f : A.X ⟶ B.X, ∀ z,
      ψ z = Additive.toMul (φ (BPAnalytic.proj Λ z)) ≫ f :=
  gaga_realization_of_dim_le_zero A B hA g Λ φ ψ hker

end CloudB3W17.ZeroDim
