import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree

/-! Positive arithmetic genus produces a nonzero regular differential. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Curve

/-- A smooth proper geometrically irreducible curve of positive genus has a
nonzero global algebraic differential. -/
theorem exists_nonzero_global_differential_of_pos_genus {k : Type u} [Field k]
    (C : Curve k)
    (h : letI : C.carrier.left.Over (Spec (.of k)) := ⟨C.carrier.hom⟩
      0 < C.carrier.left.arithmeticGenus k) :
    ∃ w : C.carrier.hom.relativeDifferentials.H 0, w ≠ 0 := by
  let X := C.carrier.left
  let _ : X.Over (Spec (.of k)) := ⟨C.carrier.hom⟩
  have : IsProper (X ↘ Spec (.of k)) := C.isProper
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := C.smoothOfRelativeDimension
  have : GeometricallyIrreducible (X ↘ Spec (.of k)) := C.geometricallyIrreducible
  have hdim := finrankH_relativeDifferentials_zero_eq_genus (baseField := k) (source := X)
  have hpos : 0 < (X ↘ Spec (.of k)).relativeDifferentials.finrankH k 0 := by
    rw [hdim]
    exact h
  change 0 < Module.finrank k (C.carrier.hom.relativeDifferentials.H 0) at hpos
  have : Nontrivial (C.carrier.hom.relativeDifferentials.H 0) :=
    Module.nontrivial_of_finrank_pos hpos
  exact exists_ne 0

end AlgebraicGeometry.Curve

#print axioms AlgebraicGeometry.Curve.exists_nonzero_global_differential_of_pos_genus
