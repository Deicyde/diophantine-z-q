/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Coefficient equality cancellation for the native triple comparison. All
coefficient objects and maps remain the actual modulesPseudofunctor objects.
This proves no global line cocycle, extension, ampleness, or NOS conclusion.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineComparison

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Canonical equality comparisons compose at the SAME actual coefficient. -/
theorem coefficientEqIso_triple {X T : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X)))
    {x y z : T ⟶ X} (hxy : x = y) (hyz : y = z) :
    (coefficientEqIso M hxy).hom ≫ (coefficientEqIso M hyz).hom =
      (coefficientEqIso M (hxy.trans hyz)).hom := by
  cases hxy
  cases hyz
  simp only [coefficientEqIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

#print axioms coefficientEqIso_triple

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
