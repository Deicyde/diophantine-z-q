-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Curve.Genus), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Basic

/-!
# Arithmetic genus and cohomological degree

The arithmetic genus of a scheme over a field is the dimension of its first
structure-sheaf cohomology. The degree of a module sheaf is the difference
between its Euler characteristic and that of the structure sheaf. These
definitions do not require a choice of rational point or projective embedding.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The arithmetic genus, defined by first structure-sheaf cohomology. -/
def arithmeticGenus : ℕ :=
  Modules.finrankH k (SheafOfModules.unit X.ringCatSheaf) 1

namespace Modules

variable {X}

/-- The cohomological degree of a module sheaf over a field. -/
def degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar k (SheafOfModules.unit X.ringCatSheaf)

/-- Isomorphic module sheaves have equal cohomological degrees. -/
theorem degree_congr {M N : X.Modules} (e : M ≅ N) : M.degree k = N.degree k := by
  simp only [degree, eulerChar_congr k e]

/-- The structure sheaf has degree zero. -/
@[simp]
theorem degree_unit : degree k (SheafOfModules.unit X.ringCatSheaf) = 0 :=
  sub_self _

end Modules

end AlgebraicGeometry.Scheme
