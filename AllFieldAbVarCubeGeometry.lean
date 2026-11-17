/-
H5 Step2 / I5a: NEW all-field edition of H72 AbVar cube geometry.
Copyright (c) 2026 H5/H72 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. No Native/kernel/Std3/current-ABI/default-budget grade.

Adapted from the FROZEN H72 native producer
L6/DefaultBudget/AbVarCubeGeometry.lean, 2187B,
SHA31d7e2c8958aaf476b4f8cef79e3528c550e12c8e4b6efb5e2090532eba3354d.
The original H72 file, module map and proof history are untouched.
Changes: new H5-owned namespace/edition, remove the unused CharZero binders,
reference characteristic-free original-name H72 producers. The four bodies
are unchanged in mathematics. No H72 CharZero theorem is used as all-field.

Parent decision B and H72 lead's exact unused-binder report were confirmed
by full Source reads of the native chain, bound to frozen hashes d38bbc54
and producer map a73cd6a8. ProductGeometry and CubeClass remain SINGLE
uncompiled Source dependencies, not copied proofs or a cached/native root.
No Source budgets, transparency or instance options are changed here.
-/
import ZInQKernel.Contrib.CloudR2Poincare.L6.ProductGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeClass

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace H5OriginalDVR.Lane2.AllFieldAbVarCubeGeometry

/-- The original abelian-variety parameter is locally Noetherian in EVERY characteristic. -/
theorem nativeAbVar_parameter_locallyNoetherian
    {k : Type u} [Field k] (J : PkgI3.AbVar k) :
    IsLocallyNoetherian J.X.left := LocallyOfFiniteType.isLocallyNoetherian J.X.hom

/-- The SAME parameter is integral over its field, hence reduced. -/
theorem nativeAbVar_parameter_reduced
    {k : Type u} [Field k] (J : PkgI3.AbVar k) :
    AlgebraicGeometry.IsReduced J.X.left := by
  haveI : AlgebraicGeometry.IsIntegral J.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  infer_instance

/-- Connectedness belongs to J, not an arbitrary test scheme. -/
theorem nativeAbVar_parameter_connected
    {k : Type u} [Field k] (J : PkgI3.AbVar k) :
    ConnectedSpace J.X.left := by
  haveI : AlgebraicGeometry.IsIntegral J.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  infer_instance

/-- Reuse the exact characteristic-free product producer on the SAME J. -/
theorem nativeAbVar_doubleFactor_geometry
    {k : Type u} [Field k] (J : PkgI3.AbVar k) :
    IsProper (J.X ⊗ J.X).hom ∧ GeometricallyIntegral (J.X ⊗ J.X).hom := by
  haveI : IsProper (fst J.X J.X).left :=
    inferInstanceAs (IsProper (pullback.fst J.X.hom J.X.hom))
  have hp : IsProper (J.X ⊗ J.X).hom := by rw [← Over.w (fst J.X J.X)]; infer_instance
  exact ⟨hp, ZInQ.Contrib.CloudR2Poincare.L6.nativeProduct_geometricallyIntegral J.X J.X⟩

end H5OriginalDVR.Lane2.AllFieldAbVarCubeGeometry
