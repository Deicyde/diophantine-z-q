-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.IdealSheaf.Multiplication), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Multiplication of ideal sheaves and base change

Extension of ideal sheaves along a scheme morphism preserves products.
On affine opens this is the corresponding statement for extension of ideals
along a ring homomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Arbitrary base change preserves products of ideal sheaves. -/
lemma comap_mul (I J : X.IdealSheafData) (f : Y ⟶ X) :
    (I * J).comap f = I.comap f * J.comap f := by
  have localEquality (point : Y) : ∃ V : Y.affineOpens, point ∈ V.1 ∧
      ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V := by
    obtain ⟨U, affineU, pointU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f point) (U := ⊤) trivial
    obtain ⟨V, affineV, pointV, inclusion⟩ :=
      exists_isAffineOpen_mem_and_subset (x := point) (U := f ⁻¹ᵁ U) pointU
    refine ⟨⟨V, affineV⟩, pointV, ?_⟩
    simp only [ideal_mul, Pi.mul_apply]
    rw [ideal_comap_appLE (I * J) f ⟨U, affineU⟩ ⟨V, affineV⟩ inclusion,
      ideal_comap_appLE I f ⟨U, affineU⟩ ⟨V, affineV⟩ inclusion,
      ideal_comap_appLE J f ⟨U, affineU⟩ ⟨V, affineV⟩ inclusion]
    simp only [ideal_mul, Pi.mul_apply, Ideal.map_mul]
  choose cover membership equality using localEquality
  exact ext_of_iSup_eq_top cover
    (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨point, membership point⟩) equality

end AlgebraicGeometry.Scheme.IdealSheafData
