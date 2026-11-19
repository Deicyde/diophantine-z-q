/-
Copyright (c) 2026 H5/H72 contributors. Apache-2.0.

# The native square on the original abelian variety

The original group, scheme and geometric fields define the same-universe
abelian-variety view. The cube relation is specialized at the identity and
two constant field-valued points. Their parameter classes vanish because
the Picard group of the field spectrum is trivial.

The resulting Picard equality yields an actual isomorphism of the original
native tensor products and pullbacks. All field characteristics, point
carriers, group laws and universe parameters remain those in the statements.
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
  letI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
  let L := Scheme.Pic.mk N
  let f : A.X ⟶ A.X := 𝟙 A.X
  let g : A.X ⟶ A.X := toUnit A.X ≫ x
  let h : A.X ⟶ A.X := toUnit A.X ≫ y
  have hc :
      Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
          Scheme.Pic.map g.left L * Scheme.Pic.map h.left L =
        Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
          Scheme.Pic.map (g * h).left L :=
    H5OriginalDVR.Lane2.AllFieldNativeCube.nativeCubeRelation
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
    change ((𝟙 A.X) * (toUnit A.X ≫ x)) * (toUnit A.X ≫ y) =
      (𝟙 A.X) * (toUnit A.X ≫ (x * y))
    rw [_root_.mul_assoc, ← MonObj.comp_mul]
  have hSquare :
      Scheme.Pic.map (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * y)) L * L =
        Scheme.Pic.map (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) L *
          Scheme.Pic.map (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A y) L := by
    have hc' := hc
    rw [hfgh, hfg, hfh] at hc'
    simpa only [hg, hh, hgh, hf, _root_.mul_one,
      H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation] using hc'
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [Scheme.Pic.mk_tensorObj, Scheme.Pic.mk_tensorObj]
  simpa only [L, Scheme.Pic.map_mk] using hSquare

/-- EXACT consumer I5a, with no square/cube/class/Factory premise.
Its proof is Source-only until the single native producer chain is admitted. -/
theorem theoremOfSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u} := by
  intro K _ _ A _ N _ x y
  exact nonempty_native_square_iso A N x y

end H5OriginalDVR.Lane2.AllFieldNativeSquare
