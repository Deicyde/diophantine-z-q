/-
# Genuine completed-field Galoisness over the canonical rational completion

The affine base is exactly Z/Q and the extension is the actual ring of integers
of the number field. A global separable splitting polynomial still splits after
completion; its roots generate the completion because their global field is dense
and the finite-dimensional generated subalgebra is closed. No local-degree count,
completed-normality premise, or Kronecker-Weber assertion is used.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Restriction
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Completed Galoisness for the actual canonical completion algebra

This is additive to the immutable completion/localization transport packet.
Its output is the field extension on the concrete types `v.adicCompletion Q`
and `w.adicCompletion L`, with `GlobalDifferentTransportCompletion`'s proved
canonical embedding and scalar towers. The integer-ring and ramification
normalizations are not changed or silently replaced by a different field model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Polynomial
open scoped NumberField GlobalDifferentTransportCompletion Valued

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- A subalgebra over the actual completed rational base containing every global field element
is all of the actual completed field. Finiteness and closure, not field density alone, justify
this algebraic-generation step. -/
theorem completedSubalgebra_eq_top_of_globalElements
    (A : Subalgebra (v.adicCompletion ℚ) (w.adicCompletion L))
    (hA : Set.range (algebraMap L (w.adicCompletion L)) ⊆ A) : A = ⊤ := by
  let := moduleFinite_numberFieldCompletion L v w
  have hclosed : IsClosed (A : Set (w.adicCompletion L)) := A.toSubmodule.closed_of_finiteDimensional
  have hdense : Dense (A : Set (w.adicCompletion L)) := (w.denseRange_algebraMap L).mono hA
  apply SetLike.coe_injective
  exact hclosed.closure_eq.symm.trans hdense.closure_eq

/-- The actual completed extension is Galois if the original number-field extension is Galois.
A separable global splitting polynomial supplies genuine completed normality; no cardinality
identity or desired local Galois assertion is assumed. -/
theorem isGalois_numberFieldCompletion [IsGalois ℚ L] :
    IsGalois (v.adicCompletion ℚ) (w.adicCompletion L) := by
  obtain ⟨p, hpsep, hpsplit⟩ := IsGalois.is_separable_splitting_field ℚ L
  let : IsSplittingField ℚ L p := hpsplit
  let p' := p.map (algebraMap ℚ (v.adicCompletion ℚ))
  have hroots : p'.rootSet (w.adicCompletion L) = p.rootSet (w.adicCompletion L) := by
    simp only [p', rootSet, aroots, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  let A := Algebra.adjoin (v.adicCompletion ℚ) (p'.rootSet (w.adicCompletion L))
  have hsub : Algebra.adjoin ℚ (p.rootSet (w.adicCompletion L)) ≤ A.restrictScalars ℚ := by
    apply Algebra.adjoin_le
    intro x hx
    change x ∈ A
    apply Algebra.subset_adjoin
    rwa [hroots]
  have hglobal : Set.range (algebraMap L (w.adicCompletion L)) ⊆ A := by
    intro x hx
    have hx' : x ∈ (Algebra.algHom ℚ L (w.adicCompletion L)).range := hx
    rw [← IsSplittingField.adjoin_rootSet_eq_range L p
      (Algebra.algHom ℚ L (w.adicCompletion L))] at hx'
    exact hsub hx'
  have hA : A = ⊤ := completedSubalgebra_eq_top_of_globalElements L v w A hglobal
  let : IsSplittingField (v.adicCompletion ℚ) (w.adicCompletion L) p' :=
    { splits' := by
        simpa only [p', Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
          ((IsSplittingField.splits L p).map (algebraMap L (w.adicCompletion L)))
      adjoin_rootSet' := hA }
  exact IsGalois.of_separable_splitting_field (p := p') hpsep.map

/-- The completed field automorphisms are continuous for the actual canonical base algebra,
by the already-proved finite-dimensionality of that extension. No normed-algebra equality
between the two normalized valuations is assumed. -/
theorem continuous_completedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) : Continuous τ := by
  let := moduleFinite_numberFieldCompletion L v w
  exact τ.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

end GlobalDifferentTransport
