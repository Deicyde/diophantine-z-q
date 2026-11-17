/-
H5 Step2 / I5a: SAME original PkgI2 object, all-field native square.
Copyright (c) 2026 H5/H72 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. No Native/kernel/Std3/current-ABI grade.

The H72 native chain was read and hash-bound to its NEW frozen v2 Source
03c11ccc/d38bbc54/a73cd6a8. CharZero was an unused inherited binder, not
mathematics. New H5 all-field geometry/global-cube editions remove only that
restriction; characteristic-free H72 cone, openness, gluing and class algebra
remain SINGLE explicit pending/uncompiled native Source producers.

This file constructs the original-u PkgI2→PkgI3 view with LITERAL SAME
Over-scheme and SAME group/proper/smooth/geometric-integral fields. It is
not the Type0 ObjBridge, not an alias or universe transfer, not a new model.
The native Picard equality is converted to an ACTUAL native module iso by
Scheme.Pic.mk_eq_mk_iff and native mk_tensorObj/map_mk. All field embeddings,
points, group law, module tensors and pullbacks remain those originally given.

The proof is cube→square at (id,const x,const y) with actual parameter classes
trivial on Spec of a field. No cube/square/Factory/ample/FBS/rank/CharZero
hypothesis. The theorem is stronger than C3 I5a: K need not be algebraically
closed. The final consumer proof uses EXACT Step1.TheoremOfSquare.{u}.

No Stacks-framework imports, Stacks↔native bridge or H72 CharZero theorem
used as an all-field theorem. Original H72 files and old H5 history unchanged.
-/
import AllFieldNativeCube
import NativeDivisorKernel
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.AllFieldNativeSquare

/-- Native-u view of the SAME original group, with each actual field preserved.
No Type0 bridge or independently constructed scheme/group is used. -/
def abVarOfGrp {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A] : PkgI3.AbVar k where
  X := A.X
  grp := A.grp
  proper := PkgI2.IsAbelianVariety.proper
  smooth := PkgI2.IsAbelianVariety.smooth
  geomInt := PkgI2.IsAbelianVariety.geomIntegral

theorem abVarOfGrp_X {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A] :
    (abVarOfGrp A).X = A.X := rfl

theorem abVarOfGrp_grp {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A] :
    (abVarOfGrp A).grp = A.grp := rfl

/-- The theorem of the square for the SAME native line on the SAME original
abelian variety, in EVERY field characteristic. No AlgClosed is required
for its given K-rational points. Native tensor/iso maps, not class aliases. -/
theorem nonempty_native_square_iso
    {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ A.X) :
    Nonempty ((Scheme.Modules.pullback
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * y))).obj N ⊗ N ≅
      (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).obj N ⊗
        (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A y)).obj N) := by
  let L := Scheme.Pic.mk N
  let f : A.X ⟶ A.X := 𝟙 A.X
  let g : A.X ⟶ A.X := toUnit A.X ≫ x
  let h : A.X ⟶ A.X := toUnit A.X ≫ y
  have hc := H5OriginalDVR.Lane2.AllFieldNativeCube.nativeCubeRelation
    (abVarOfGrp A) A.X f g h L
  have hg : Scheme.Pic.map g.left L = 1 := by
    dsimp only [g]
    rw [Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one (toUnit A.X).left x.left L
  have hh : Scheme.Pic.map h.left L = 1 := by
    dsimp only [h]
    rw [Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one (toUnit A.X).left y.left L
  have hgh : Scheme.Pic.map (g * h).left L = 1 := by
    have hfac : g * h = toUnit A.X ≫ (x * y) := by
      dsimp only [g, h]
      rw [← MonObj.comp_mul]
    rw [hfac, Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one
      (toUnit A.X).left (x * y).left L
  have hf : Scheme.Pic.map f.left L = L := by
    change Scheme.Pic.map (𝟙 A.X.left) L = L
    exact Scheme.Pic.map_id L
  have hfg : f * g = H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x := rfl
  have hfh : f * h = H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A y := rfl
  have hfgh : f * g * h =
      H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A (x * y) := by
    dsimp only [f, g, h]
    rw [mul_assoc, ← MonObj.comp_mul]
    rfl
  rw [hg, hh, hgh, hf, hfg, hfh, hfgh, mul_one, mul_one, mul_one] at hc
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [Scheme.Pic.mk_tensorObj, Scheme.Pic.mk_tensorObj]
  simpa only [L, H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation,
    Scheme.Pic.map_mk] using hc

/-- EXACT consumer I5a, with no square/cube/class/Factory premise.
Its proof is Source-only until the single native producer chain is admitted. -/
theorem theoremOfSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u} := by
  intro K _ _ A _ N _ x y
  exact nonempty_native_square_iso A N x y

end H5OriginalDVR.Lane2.AllFieldNativeSquare
