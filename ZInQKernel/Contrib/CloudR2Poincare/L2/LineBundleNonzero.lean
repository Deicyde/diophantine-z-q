import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmple
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Endomorphism
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Hom
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Native line-bundle nonzero maps: the properness part of Mumford's contradiction

The source APIs are the already published Jacobian-Challenge sheaf model;
no Stacks Picard comparison, general dual, or desired ampleness fact is used.
The nonzero morphism identifies its source with a Cartier ideal, whose inclusion
is mono. A pair of nonzero maps to and from O_X then gives a nonzero scalar
endomorphism of O_X, which is invertible on a proper integral scheme over a field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Every nonzero map from a line bundle to O_X on an integral scheme is mono,
by its identification with the ideal of its effective Cartier zero divisor. -/
theorem mono_lineBundle_to_unit_of_ne_zero {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules) [M.IsInvertible] (t : M ⟶ unit X) (ht : t ≠ 0) : Mono t := by
  obtain ⟨κ, hκ⟩ := t.exists_iso_toModules_zeroLocus (t.isInvertible_zeroLocus ht)
  have h : Mono (κ.hom ≫ t.zeroLocus.toModulesι) := inferInstance
  rw [hκ] at h
  exact h

/-- Multiplication by a global unit is an isomorphism on a module sheaf. -/
theorem isIso_smulHom_of_isUnit {X : Scheme.{u}} (M : X.Modules)
    (c : Γ(X, ⊤)) (hc : IsUnit c) : IsIso (M.smulHom c) := by
  obtain ⟨c, rfl⟩ := hc
  refine ⟨⟨M.smulHom (↑c⁻¹), ?_, ?_⟩⟩
  · rw [← smulHom_mul, Units.inv_mul, smulHom_one]
  · rw [← smulHom_mul, Units.mul_inv, smulHom_one]

/-- A line bundle on a proper integral scheme with nonzero maps O_X→M and M→O_X
is trivial. This is the native sheaf-category form of the nonzero-sections
criterion used by the seesaw principle. -/
theorem nonempty_iso_unit_of_nonzero_maps {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X]
    (M : X.Modules) [M.IsInvertible]
    (s : unit X ⟶ M) (t : M ⟶ unit X) (hs : s ≠ 0) (ht : t ≠ 0) :
    Nonempty (M ≅ unit X) := by
  letI : Mono t := mono_lineBundle_to_unit_of_ne_zero M t ht
  have hst : s ≫ t ≠ 0 := by
    intro h
    apply hs
    apply (cancel_mono t).mp
    simpa only [zero_comp] using h
  obtain ⟨c, hc⟩ := exists_eq_smulHom (unit X) (s ≫ t)
  have hc0 : c ≠ 0 := by
    intro h
    apply hst
    rw [hc, h, smulHom_zero]
  letI : Field Γ(X, ⊤) := (isField_of_universallyClosed k p).toField
  haveI : IsIso (s ≫ t) := by
    rw [hc]
    exact isIso_smulHom_of_isUnit (unit X) c (isUnit_iff_ne_zero.mpr hc0)
  let invt : unit X ⟶ M := inv (s ≫ t) ≫ s
  have hinvt : invt ≫ t = 𝟙 (unit X) := by
    dsimp [invt]
    rw [Category.assoc, IsIso.inv_hom_id]
  have htinv : t ≫ invt = 𝟙 M := by
    apply (cancel_mono t).mp
    rw [Category.assoc, hinvt, Category.comp_id, Category.id_comp]
  haveI : IsIso t := ⟨⟨invt, htinv, hinvt⟩⟩
  exact ⟨asIso t⟩

end ZInQ.Contrib.CloudR2Poincare.L2
