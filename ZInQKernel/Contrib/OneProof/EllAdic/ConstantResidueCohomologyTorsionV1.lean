import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian

namespace RC53.EllAdic

universe u v w s

private theorem map_nsmul_id_eq_zero
    {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (X : C) (k : ℕ)
    (h : k • 𝟙 X = 0) : k • 𝟙 (F.obj X) = 0 := by
  calc
    k • 𝟙 (F.obj X) = F.map (k • 𝟙 X) := by rw [F.map_nsmul, F.map_id]
    _ = 0 := by rw [h, F.map_zero]

/-- An additive functor to abelian groups preserves the exponent bound. -/
theorem addCommGrp_nsmul_eq_zero_of_map
    {C : Type*} [Category* C] [Preadditive C]
    (F : C ⥤ Ab.{w}) [F.Additive] (X : C) (k : ℕ)
    (h : k • 𝟙 X = 0) (x : F.obj X) : k • x = 0 := by
  have hh := map_nsmul_id_eq_zero F X k h
  have hval := congrArg (fun f : F.obj X ⟶ F.obj X => f.hom x) hh
  change k • x = 0 at hval
  exact hval

/-- The actual sheaf cohomology of the constant sheaf on the lifted residue
coefficient is annihilated by its modulus. This includes the zero-depth case. -/
theorem liftedZMod_constantSheaf_cohomology_nsmul_eq_zero
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{w}] [HasExt.{s} (Sheaf J Ab.{w})]
    (k i : ℕ) (x : (((constantSheaf J Ab.{w}).obj
      (AddCommGrpCat.of (ULift.{w} (ZMod k)))).H i : Type s)) : k • x = 0 := by
  let A : Ab.{w} := AddCommGrpCat.of (ULift.{w} (ZMod k))
  have hA : k • 𝟙 A = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro y
    change k • y = 0
    apply ULift.down_injective
    change k • (y.down : ZMod k) = 0
    exact ZModModule.char_nsmul_eq_zero k y.down
  let H : Sheaf J Ab.{w} ⥤ Ab.{s} := Sheaf.functorH J i
  exact addCommGrp_nsmul_eq_zero_of_map H ((constantSheaf J Ab.{w}).obj A) k
    (map_nsmul_id_eq_zero (constantSheaf J Ab.{w}) A k hA) x

end RC53.EllAdic
