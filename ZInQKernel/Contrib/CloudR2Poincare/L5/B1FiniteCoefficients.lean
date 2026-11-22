import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# B1: all-degree finite constant coefficients in native cohomology

This constructs the actual sheaf isomorphism N tensor O_X^I = direct-sum_I N
and proves its cohomology rank in every degree. The tensor/coproduct comparison
is constructed using the proved tensor equivalence for an invertible N. No
Kunneth rank equality, product-vanishing statement, or desired Fact is assumed.

The scalar/cohomology API is the native W07 underlying-abelian-sheaf Ext API,
not a renamed classical-derived-evaluation group.
Original lane-local proof, reusing already vendored W07 and pinned Mathlib.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules BigOperators

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- A finite coproduct of module sheaves is an actual biproduct. This local
instance is proved from the existing colimit, not an additional assumption. -/
theorem finiteModulesBiproduct {X : Scheme.{u}} {I : Type u} [Finite I]
    (family : I → X.Modules) : HasBiproduct family :=
  HasBiproduct.of_hasCoproduct family

attribute [local instance] finiteModulesBiproduct

/-- The actual finite constant-coefficient sheaf isomorphism. -/
def tensorFiniteFreeIso {X : Scheme.{u}} (N : X.Modules) [N.IsInvertible]
    (I : Type u) [Fintype I] :
    N ⊗ SheafOfModules.free (R := X.ringCatSheaf) I ≅ ⨁ fun _ : I => N :=
  PreservesCoproduct.iso (tensorLeft N) (fun _ : I => SheafOfModules.unit X.ringCatSheaf) ≪≫
    Sigma.mapIso (fun _ : I => ρ_ N) ≪≫
      (biproduct.isoCoproduct (fun _ : I => N)).symm

/-- Every native cohomological rank with finite constant coefficients is
multiplied by the coefficient dimension. It applies in particular to the
constant free terms of a native finite-free cohomology model. -/
theorem native_finrankH_tensor_finiteFree
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (N : X.Modules) [N.IsInvertible] (I : Type u) [Fintype I]
    (q : ℕ) [Module.Finite k (N.H q)] :
    (N ⊗ SheafOfModules.free (R := X.ringCatSheaf) I).finrankH k q =
      Fintype.card I * N.finrankH k q := by
  calc
    (N ⊗ SheafOfModules.free (R := X.ringCatSheaf) I).finrankH k q =
        (⨁ fun _ : I => N).finrankH k q :=
      Scheme.Modules.finrankH_congr k (tensorFiniteFreeIso N I) q
    _ = ∑ _ : I, N.finrankH k q :=
      Scheme.Modules.finrankH_of_isBilimit k (biproduct.isBilimit (fun _ : I => N)) q
    _ = Fintype.card I * N.finrankH k q := by simp

end ZInQ.Contrib.CloudR2Poincare.L5
