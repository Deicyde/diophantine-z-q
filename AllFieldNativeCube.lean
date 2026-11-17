/-
H5 Step2 / I5a: NEW all-field native global cube-class edition.
Copyright (c) 2026 H5/H72 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. No Native/kernel/Std3/current-ABI acceptance.

Adapted ONLY the binder-carrying global-cube part of H72
L6/CubeTheorem.lean, 12226B,
SHA50d972d86d60ff06c62705ef7bc61d8239d520125486cef7215699f0fe08e013.
Unused CharZero is removed; H72's frozen Source is not edited or regraded.
The existing characteristic-free L2 actual-cone semicontinuity03c11ccc,
L6 isOpen_cubeFibreTrivialitySet50d972d8, CubeClasscd49c11c,
CubeGeometry789e0fce, ReducedCubeGluinga54fac1e and field detection7ff3d5a4
are SINGLE native Source producers. Their proofs are neither copied nor
invoked from historical native objects. The original module-name mapping
is a73cd6a8; no root/prefix/runtime activation is performed.

The reused openness has TWO ENTIRE pointed product faces. It is not C3's
refuted one-slice seesaw-openness proposition. Reduced global normalization
is applied to parameter J itself, whose geometry is proved in the new
all-field edition. No cube/square/model/Fact/Factory is an input.

This is native W07 Picard-class mathematics in symbolic u, all fields.
No Stacks-framework predicate or Stacks↔native bridge is imported.
Actual module-isomorphism I5a and the original PkgI2 object adapter are in
the following separate H5 file, not inferred by a raw alias here.
-/
import AllFieldAbVarCubeGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeTheorem

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
  MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.CloudR2Poincare.L6
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.AllFieldNativeCube

private theorem cube_faceXR_eq_coordinate_two
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    nativeCubeFaceXR A.hom A.hom A.hom η[A].left
        (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) = (nativeCubeFace₂ A).left := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [nativeCubeFaceXR, nativeCubeFaceXBase, nativeCubeFace₂, Category.assoc]
    · simp [nativeCubeFaceXR, nativeCubeFaceXBase, nativeCubeFace₂,
        Hom.one_def, Category.assoc]
  · simp [nativeCubeFaceXR, nativeCubeFace₂, Category.assoc]

private theorem cube_faceYR_eq_coordinate_one
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    nativeCubeFaceYR A.hom A.hom A.hom η[A].left
        (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) = (nativeCubeFace₁ A).left := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [nativeCubeFaceYR, nativeCubeFaceYBase, nativeCubeFace₁,
        Hom.one_def, Category.assoc]
    · simp [nativeCubeFaceYR, nativeCubeFaceYBase, nativeCubeFace₁,
        ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over, Category.assoc]
  · simp [nativeCubeFaceYR, nativeCubeFace₁, Category.assoc]

private theorem cube_unit_baseChange_factors_through_third_face
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (T : Over (Spec (.of k))) :
    JacobianChallenge.baseChangeMap (A ⊗ A).hom (1 : T ⟶ A) =
      pullback.fst (A ⊗ A).hom T.hom ≫ (nativeCubeFace₃ A).left := by
  apply pullback.hom_ext
  · simp [JacobianChallenge.baseChangeMap, nativeCubeFace₃, Category.assoc]
  · simp only [JacobianChallenge.baseChangeMap, nativeCubeFace₃,
      Hom.one_def, Over.comp_left, Over.toUnit_left, Over.lift_left,
      Over.snd_left, Category.assoc, pullback.lift_snd, pullback.lift_fst,
      Over.tensorObj_hom]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ η[A].left)
      (pullback.condition (A ⊗ A).hom T.hom).symm

/-- NEW all-field edition: true cube-class triviality from the three entire
coordinate faces on the SAME abelian variety. No characteristic assumption. -/
theorem nativeCubePicardClass_eq_one_of_three_faces
    {k : Type u} [Field k] (J : PkgI3.AbVar k)
    (N : (nativeCubeObj J.X).left.Pic)
    (h₁ : Scheme.Pic.map (nativeCubeFace₁ J.X).left N = 1)
    (h₂ : Scheme.Pic.map (nativeCubeFace₂ J.X).left N = 1)
    (h₃ : Scheme.Pic.map (nativeCubeFace₃ J.X).left N = 1) : N = 1 := by
  let A := J.X
  let f := A.hom
  let π := pullback.fst f f ≫ f
  let σ := nativeCubePoint f f η[A].left (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)
    η[A].left (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)
  have hσ : σ ≫ π = 𝟙 _ :=
    nativeCubePoint_struct f f η[A].left (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)
      η[A].left (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)
  obtain ⟨hp, hf, hi⟩ := ZInQ.Contrib.CloudR2Poincare.L4.CubeFaces.nativeCubeProduct_geometry f f
  letI : IsProper π := hp
  letI : Flat π := hf
  letI : GeometricallyIntegral π := hi
  letI : IsLocallyNoetherian A.left :=
    H5OriginalDVR.Lane2.AllFieldAbVarCubeGeometry.nativeAbVar_parameter_locallyNoetherian J
  letI : AlgebraicGeometry.IsReduced A.left :=
    H5OriginalDVR.Lane2.AllFieldAbVarCubeGeometry.nativeAbVar_parameter_reduced J
  letI : ConnectedSpace A.left :=
    H5OriginalDVR.Lane2.AllFieldAbVarCubeGeometry.nativeAbVar_parameter_connected J
  have hX : Scheme.Pic.map (nativeCubeFaceXR f f A.hom η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)) N = 1 := by
    rw [cube_faceXR_eq_coordinate_two]
    exact h₂
  have hY : Scheme.Pic.map (nativeCubeFaceYR f f A.hom η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A)) N = 1 := by
    rw [cube_faceYR_eq_coordinate_one]
    exact h₁
  have hNorm : Scheme.Pic.map
      (sectionBaseChange π σ hσ A) N = 1 :=
    nativeCube_normalized_of_faceX f f A.hom η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) N hX
  have hOpen : IsOpen (ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π A.hom) N) :=
    isOpen_cubeFibreTrivialitySet f f η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) η[A].left
      (ZInQ.Contrib.CloudR2Poincare.L1.groupUnit_over A) A N hX hY
  let unitTest : ZInQ.Contrib.CloudR2Poincare.L1.fieldTest k k ⟶ A := 1
  have hAtUnit : Scheme.Pic.map (JacobianChallenge.baseChangeMap π unitTest) N = 1 := by
    rw [cube_unit_baseChange_factors_through_third_face A
        (ZInQ.Contrib.CloudR2Poincare.L1.fieldTest k k),
      Scheme.Pic.map_comp, h₃, Scheme.Pic.map_one]
  have hUnitMem :=
    (ZInQ.Contrib.CloudR2Poincare.L2.fibreTriviality_mem_fieldTest_iff
      π σ hσ A N hNorm unitTest).mpr hAtUnit
  have hNonempty : (ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π A.hom) N).Nonempty := by
    refine ⟨unitTest.left (IsLocalRing.closedPoint k), ?_⟩
    exact hUnitMem
  exact normalizedPicardClass_eq_one_of_open_fibreTriviality π σ hσ A N hNorm hOpen hNonempty

/-- The same seven-factor native class is one in all characteristics.
Faces, actual-cone openness and reduced gluing are single native producers. -/
theorem nativeCubeClass_eq_one
    {k : Type u} [Field k] (J : PkgI3.AbVar k) (L : J.X.left.Pic) :
    nativeCubeClass J.X L = 1 :=
  nativeCubePicardClass_eq_one_of_three_faces J (nativeCubeClass J.X L)
    (nativeCubeClass_face₁ J.X L) (nativeCubeClass_face₂ J.X L) (nativeCubeClass_face₃ J.X L)

/-- All-field native cube relation on ANY test scheme, by pullback of the
actual global class; no reducedness/noetherian condition on that test. -/
theorem nativeCubeRelation
    {k : Type u} [Field k] (J : PkgI3.AbVar k)
    (P : Over (Spec (.of k))) (f g h : P ⟶ J.X) (L : J.X.left.Pic) :
    Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
        Scheme.Pic.map g.left L * Scheme.Pic.map h.left L =
      Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
        Scheme.Pic.map (g * h).left L :=
  nativeCubeRelation_of_class_eq_one J.X L (nativeCubeClass_eq_one J L) P f g h

end H5OriginalDVR.Lane2.AllFieldNativeCube
