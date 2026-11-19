import ZInQKernel.HDecomp.Objects
import InertiaBridgeV002
import TameGeneratorConditionalV001

/-!
# The tame generator in the objects of the wild-inertia leaf

The kernel predicate `PkgI2.IsInertia w σ` (membership in Mathlib's inertia subgroup) is exactly
membership in the actual inertia group `inertiaGroup w`; the wild condition of the leaf
(`∀ x ≠ 0, v(σ x - x) < v(x)`) is literally membership in `wildGroup w`. In the setting of the
leaf (`K` a number field, `O` a discrete valuation ring of `K`, `Ω` an algebraic closure, `w`
over `O`), the generic procyclicity statement and finite-layer tame cyclicity produce an actual
inertia element `τ` such that every inertia element agrees on every finite Galois layer with
`τ ^ k π` for an actual strict-displacement `π`.
-/

noncomputable section
set_option autoImplicit false

namespace ActualTameInertia

theorem isInertia_iff {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    PkgI2.IsInertia w σ ↔ σ ∈ inertiaGroup w :=
  (mem_inertiaGroup_iff_inertiaSubgroup w σ).symm

/-- **Tame generator in the leaf's objects** (conditional on the two exact inputs). -/
theorem leaf_tame_generator_of (hproc : ProcyclicStatement.{0})
    (K : Type) [Field K] [NumberField K] (O : ValuationSubring K)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (hfin : FiniteLayerTameCyclic K Ω O) :
    ∃ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ ∧ ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
      ∀ L : FiniteGaloisIntermediateField K Ω, ∃ k : ℤ, ∃ π : Ω ≃ₐ[K] Ω,
        (∀ x : Ω, x ≠ 0 → w.valuation (π x - x) < w.valuation x) ∧
          AlgEquiv.restrictNormalHom L.toIntermediateField (τ ^ k * π) =
            AlgEquiv.restrictNormalHom L.toIntermediateField σ := by
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  obtain ⟨τ, hτ⟩ := exists_tame_generator_layers_of hproc O w hw hfin
  have hτI : PkgI2.IsInertia w (τ : Ω ≃ₐ[K] Ω) := (isInertia_iff w (τ : Ω ≃ₐ[K] Ω)).2 τ.2
  refine ⟨τ, hτI, fun σ hσ L => ?_⟩
  obtain ⟨k, π, hπ, h⟩ := hτ ⟨σ, (isInertia_iff w σ).1 hσ⟩ L
  refine ⟨k, π, hπ, ?_⟩
  rw [map_mul]
  exact h

end ActualTameInertia

#print axioms ActualTameInertia.isInertia_iff
#print axioms ActualTameInertia.leaf_tame_generator_of
