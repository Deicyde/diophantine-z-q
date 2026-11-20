import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeClass
import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L6.AbVarCubeGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L6.PositiveFiberCriterion
import ZInQKernel.Contrib.CloudR2Poincare.L4.CubeFaces.Family
import ZInQKernel.Contrib.CloudR2Poincare.L2.FieldTrivialityDetection
import ZInQKernel.Contrib.CloudR2Poincare.L2.CubeConeFibreIntegration

/-!
# Native theorem of the cube on the actual triple product

The two-face cone bounds for a line bundle and its dual give openness of
residue-fibre triviality. On the actual triple product, connectedness and
normalized reduced seesaw identify the seven-factor class with the unit.
No model, rank, Picard-zero, square or cube proposition is assumed by the
final theorem.

The parameter used in the reduced global seesaw is J itself. Only after the
actual class on J cubed is proved trivial is it pulled back to arbitrary
test schemes.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Pullback of the native dual has the same actual Picard class as the dual
of the pulled-back module. The coefficient isomorphism is obtained from that
actual class equality, never from a dimension-selected vector-space model. -/
private theorem cube_dual_fibre_finrank
    {K : Type u} [Field K] {Q F : Scheme.{u}}
    (r : F ⟶ Spec (.of K)) (a : F ⟶ Q)
    (M : Q.Modules) [M.IsInvertible] :
    letI : F.Over (Spec (.of K)) := ⟨r⟩
    Module.finrank K (((Scheme.Modules.pullback a).obj Mᵛ).H 0) =
      Module.finrank K ((((Scheme.Modules.pullback a).obj M)ᵛ).H 0) := by
  letI : F.Over (Spec (.of K)) := ⟨r⟩
  let N := (Scheme.Modules.pullback a).obj M
  let D := (Scheme.Modules.pullback a).obj Mᵛ
  have hD : Scheme.Pic.mk D = Scheme.Pic.mk Nᵛ := by
    calc
      Scheme.Pic.mk D = Scheme.Pic.map a (Scheme.Pic.mk Mᵛ) :=
        (Scheme.Pic.map_mk a Mᵛ).symm
      _ = (Scheme.Pic.map a (Scheme.Pic.mk M))⁻¹ := by
        rw [Scheme.Pic.mk_dual, L1.pic_map_inv]
      _ = (Scheme.Pic.mk N)⁻¹ := by rw [Scheme.Pic.map_mk]
      _ = Scheme.Pic.mk Nᵛ := (Scheme.Pic.mk_dual N).symm
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff D Nᵛ).mp hD
  exact Scheme.Modules.finrankH_congr K e 0

/-- Actual residue-fibre triviality from the two derived cohomology bounds.
This private bridge uses the original residue field and the original fibre
inclusion, and transports the dual coefficient by an actual module iso. -/
private theorem cube_fibreClass_eq_one_of_bounds
    {Q T : Scheme.{u}} (q : Q ⟶ T) [IsProper q] [GeometricallyIntegral q]
    (M : Q.Modules) [M.IsInvertible] (z : T)
    (hM : letI : (q.fiber z).Over (Spec (T.residueField z)) :=
      ⟨q.fiberToSpecResidueField z⟩
      1 ≤ Module.finrank (T.residueField z)
        (((Scheme.Modules.pullback (q.fiberι z)).obj M).H 0))
    (hD : letI : (q.fiber z).Over (Spec (T.residueField z)) :=
      ⟨q.fiberToSpecResidueField z⟩
      1 ≤ Module.finrank (T.residueField z)
        (((Scheme.Modules.pullback (q.fiberι z)).obj Mᵛ).H 0)) :
    Scheme.Pic.map (q.fiberι z) (Scheme.Pic.mk M) = 1 := by
  let r := q.fiberToSpecResidueField z
  let a := q.fiberι z
  let P := (Scheme.Modules.pullback a).obj M
  letI : (q.fiber z).Over (Spec (T.residueField z)) := ⟨r⟩
  have fibreSquare : IsPullback a r q (T.fromSpecResidueField z) :=
    IsPullback.of_hasPullback q (T.fromSpecResidueField z)
  haveI hrP : IsProper r :=
    MorphismProperty.of_isPullback (P := @IsProper) fibreSquare
      (inferInstance : IsProper q)
  haveI hrG : GeometricallyIntegral r :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) fibreSquare
      (inferInstance : GeometricallyIntegral q)
  haveI : IsProper ((q.fiber z) ↘ Spec (T.residueField z)) :=
    inferInstanceAs (IsProper r)
  haveI : GeometricallyIntegral ((q.fiber z) ↘ Spec (T.residueField z)) :=
    inferInstanceAs (GeometricallyIntegral r)
  have hP : 1 ≤ Module.finrank (T.residueField z) (P.H 0) := hM
  have hPD : 1 ≤ Module.finrank (T.residueField z) (Pᵛ.H 0) := by
    calc
      1 ≤ Module.finrank (T.residueField z)
          (((Scheme.Modules.pullback a).obj Mᵛ).H 0) := hD
      _ = Module.finrank (T.residueField z) (Pᵛ.H 0) := cube_dual_fibre_finrank r a M
  letI hPinv : P.IsInvertible := inferInstance
  have hclass : Scheme.Pic.mk P = 1 :=
    @nativePicardClass_eq_one_of_positiveHZero_dual
      (T.residueField z) (inferInstance : Field (T.residueField z))
      (q.fiber z) r hrP hrG P hPinv hP hPD
  rw [Scheme.Pic.map_mk]
  exact hclass

/-- Openness of the literal residue-fibre triviality locus of the actual
pointed product family. The positive cohomology bounds are proved by the L2
actual-cone integration, for M and its native dual separately. -/
theorem isOpen_cubeFibreTrivialitySet
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left]
    (N : (pullback (pullback.fst f g ≫ f) T.hom).Pic)
    (hX : Scheme.Pic.map (nativeCubeFaceXR f g T.hom y hy) N = 1)
    (hY : Scheme.Pic.map (nativeCubeFaceYR f g T.hom x hx) N = 1) :
    IsOpen (L2.fibrePicardTrivialitySet
      (pullback.snd (pullback.fst f g ≫ f) T.hom) N) := by
  classical
  let q := pullback.snd (pullback.fst f g ≫ f) T.hom
  obtain ⟨hp, hf, hi⟩ := L4.CubeFaces.nativeCubeFamily_geometry f g T.hom
  letI : IsProper q := hp
  letI : Flat q := hf
  letI : GeometricallyIntegral q := hi
  obtain ⟨M, hM, hrep⟩ := Scheme.Pic.exists_mk_eq N
  letI : M.IsInvertible := hM
  have hMX : Scheme.Pic.map (nativeCubeFaceXR f g T.hom y hy) (Scheme.Pic.mk M) = 1 := by
    rw [hrep]
    exact hX
  have hMY : Scheme.Pic.map (nativeCubeFaceYR f g T.hom x hx) (Scheme.Pic.mk M) = 1 := by
    rw [hrep]
    exact hY
  have hDX : Scheme.Pic.map (nativeCubeFaceXR f g T.hom y hy) (Scheme.Pic.mk Mᵛ) = 1 := by
    rw [Scheme.Pic.mk_dual, L1.pic_map_inv, hMX, inv_one]
  have hDY : Scheme.Pic.map (nativeCubeFaceYR f g T.hom x hx) (Scheme.Pic.mk Mᵛ) = 1 := by
    rw [Scheme.Pic.mk_dual, L1.pic_map_inv, hMY, inv_one]
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have htM : Scheme.Pic.map (q.fiberι t) (Scheme.Pic.mk M) = 1 := by
    rw [hrep]
    exact ht
  have htD : Scheme.Pic.map (q.fiberι t) (Scheme.Pic.mk Mᵛ) = 1 := by
    rw [Scheme.Pic.mk_dual, L1.pic_map_inv, htM, inv_one]
  obtain ⟨VM, htM', hVM⟩ :=
    L2.CubeConeFibreIntegration.exists_open_cubeFibreHZero_ge_one
      f g x hx y hy T M hMX hMY t htM
  obtain ⟨VD, htD', hVD⟩ :=
    L2.CubeConeFibreIntegration.exists_open_cubeFibreHZero_ge_one
      f g x hx y hy T Mᵛ hDX hDY t htD
  let V : T.left.Opens := VM ⊓ VD
  have htV : t ∈ V := ⟨htM', htD'⟩
  apply Filter.mem_of_superset (V.isOpen.mem_nhds htV)
  intro z hz
  have hclass : Scheme.Pic.map (q.fiberι z) (Scheme.Pic.mk M) = 1 :=
    cube_fibreClass_eq_one_of_bounds q M z (hVM z hz.1) (hVD z hz.2)
  change Scheme.Pic.map (q.fiberι z) N = 1
  rw [← hrep]
  exact hclass

/-- The actual X-family face over parameter A is the second coordinate face
of A cubed; both use precisely the same canonical native pullbacks. -/
private theorem cube_faceXR_eq_coordinate_two
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    nativeCubeFaceXR A.hom A.hom A.hom η[A].left (L1.groupUnit_over A) =
      (nativeCubeFace₂ A).left := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [nativeCubeFaceXR, nativeCubeFaceXBase, nativeCubeFace₂, Category.assoc]
    · simp [nativeCubeFaceXR, nativeCubeFaceXBase, nativeCubeFace₂,
        Hom.one_def, Category.assoc]
  · simp [nativeCubeFaceXR, nativeCubeFace₂, Category.assoc]

/-- The actual Y-family face over parameter A is the first coordinate face. -/
private theorem cube_faceYR_eq_coordinate_one
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    nativeCubeFaceYR A.hom A.hom A.hom η[A].left (L1.groupUnit_over A) =
      (nativeCubeFace₁ A).left := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [nativeCubeFaceYR, nativeCubeFaceYBase, nativeCubeFace₁,
        Hom.one_def, Category.assoc]
    · simp [nativeCubeFaceYR, nativeCubeFaceYBase, nativeCubeFace₁,
        L1.groupUnit_over, Category.assoc]
  · simp [nativeCubeFaceYR, nativeCubeFace₁, Category.assoc]

/-- Restriction to the actual unit-valued parameter factors through the
third coordinate face. No equality of k with a residue-field dictionary is
assumed; field-test detection below handles that comparison canonically. -/
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
    simpa only [Category.assoc, Over.tensorObj_hom] using congrArg (fun a => a ≫ η[A].left)
      (pullback.condition (f := (A ⊗ A).hom) (g := T.hom)).symm

/-- The actual Picard class on J cubed is one when its three entire
coordinate faces are trivial. Openness is proved above; closedness,
connectedness and reduced normalized seesaw are retained native suppliers. -/
theorem nativeCubePicardClass_eq_one_of_three_faces
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (N : (nativeCubeObj J.X).left.Pic)
    (h₁ : Scheme.Pic.map (nativeCubeFace₁ J.X).left N = 1)
    (h₂ : Scheme.Pic.map (nativeCubeFace₂ J.X).left N = 1)
    (h₃ : Scheme.Pic.map (nativeCubeFace₃ J.X).left N = 1) : N = 1 := by
  let A := J.X
  let f := A.hom
  let π := pullback.fst f f ≫ f
  let σ := nativeCubePoint f f η[A].left (L1.groupUnit_over A)
    η[A].left (L1.groupUnit_over A)
  have hσ : σ ≫ π = 𝟙 _ :=
    nativeCubePoint_struct f f η[A].left (L1.groupUnit_over A)
      η[A].left (L1.groupUnit_over A)
  obtain ⟨hp, hf, hi⟩ := L4.CubeFaces.nativeCubeProduct_geometry f f
  letI : IsProper π := hp
  letI : Flat π := hf
  letI : GeometricallyIntegral π := hi
  letI : IsLocallyNoetherian A.left := nativeAbVar_parameter_locallyNoetherian J
  letI : AlgebraicGeometry.IsReduced A.left := nativeAbVar_parameter_reduced J
  letI : ConnectedSpace A.left := nativeAbVar_parameter_connected J
  have hX : Scheme.Pic.map (nativeCubeFaceXR f f A.hom η[A].left (L1.groupUnit_over A)) N = 1 := by
    rw [cube_faceXR_eq_coordinate_two]
    exact h₂
  have hY : Scheme.Pic.map (nativeCubeFaceYR f f A.hom η[A].left (L1.groupUnit_over A)) N = 1 := by
    rw [cube_faceYR_eq_coordinate_one]
    exact h₁
  have hNorm : Scheme.Pic.map (sectionBaseChange π σ hσ A) N = 1 :=
    nativeCube_normalized_of_faceX f f A.hom η[A].left (L1.groupUnit_over A)
      η[A].left (L1.groupUnit_over A) N hX
  have hOpen : IsOpen (L2.fibrePicardTrivialitySet (pullback.snd π A.hom) N) :=
    isOpen_cubeFibreTrivialitySet f f η[A].left (L1.groupUnit_over A)
      η[A].left (L1.groupUnit_over A) A N hX hY
  let unitTest : L1.fieldTest k k ⟶ A := 1
  have hAtUnit : Scheme.Pic.map (JacobianChallenge.baseChangeMap π unitTest) N = 1 := by
    have hbc : JacobianChallenge.baseChangeMap π unitTest =
        JacobianChallenge.baseChangeMap (A ⊗ A).hom (1 : L1.fieldTest k k ⟶ A) := rfl
    rw [hbc, cube_unit_baseChange_factors_through_third_face A (L1.fieldTest k k),
      Scheme.Pic.map_comp, h₃, Scheme.Pic.map_one]
  have hUnitMem :=
    (L2.fibreTriviality_mem_fieldTest_iff π σ hσ A N hNorm unitTest).mpr hAtUnit
  have hNonempty : (L2.fibrePicardTrivialitySet (pullback.snd π A.hom) N).Nonempty := by
    refine ⟨unitTest.left (IsLocalRing.closedPoint k), ?_⟩
    exact hUnitMem
  exact normalizedPicardClass_eq_one_of_open_fibreTriviality π σ hσ A N hNorm hOpen hNonempty

/-- The literal seven-factor cube class of any line-bundle class on the
actual abelian variety is trivial, with no supplied cube/square premise. -/
theorem nativeCubeClass_eq_one
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (L : J.X.left.Pic) : nativeCubeClass J.X L = 1 :=
  nativeCubePicardClass_eq_one_of_three_faces J (nativeCubeClass J.X L)
    (nativeCubeClass_face₁ J.X L) (nativeCubeClass_face₂ J.X L) (nativeCubeClass_face₃ J.X L)

end ZInQ.Contrib.CloudR2Poincare.L6
