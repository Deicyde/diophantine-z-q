/-
Multiplication-etale construction: ActualStalkWorld.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.OriginCanonicalTangent
import ZInQKernel.Contrib.MulEtale.Direct.ActualVanishingDictionary

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace H101DirectFieldRoute.ActualTransport

universe u

variable {X B : Scheme.{u}}

abbrev BaseStalk (p : X ⟶ B) (f : X ⟶ X) (x : X) : Type u :=
  B.presheaf.stalk (p (f x))

abbrev SourceStalk (f : X ⟶ X) (x : X) : Type u :=
  X.presheaf.stalk (f x)

abbrev TargetStalk (x : X) : Type u := X.presheaf.stalk x
abbrev PointField (x : X) : Type u := X.residueField x

abbrev actualStalkHom (f : X ⟶ X) (x : X) :
    SourceStalk f x →+* TargetStalk x := (f.stalkMap x).hom

abbrev baseSourceHom (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    BaseStalk p f x →+* SourceStalk f x := (p.stalkMap (f x)).hom

abbrev baseTargetHom (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    BaseStalk p f x →+* TargetStalk x :=
  (actualStalkHom f x).comp (baseSourceHom p f x)

abbrev residueHom (x : X) : TargetStalk x →+* PointField x := (X.residue x).hom

abbrev sourceCoeffHom (f : X ⟶ X) (x : X) :
    SourceStalk f x →+* PointField x :=
  (residueHom x).comp (actualStalkHom f x)

abbrev baseCoeffHom (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    BaseStalk p f x →+* PointField x :=
  (residueHom x).comp (baseTargetHom p f x)

scoped instance actualStalkAlgebra (f : X ⟶ X) (x : X) :
    Algebra (SourceStalk f x) (TargetStalk x) := (actualStalkHom f x).toAlgebra

scoped instance baseSourceAlgebra (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    Algebra (BaseStalk p f x) (SourceStalk f x) := (baseSourceHom p f x).toAlgebra

scoped instance baseTargetAlgebra (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    Algebra (BaseStalk p f x) (TargetStalk x) := (baseTargetHom p f x).toAlgebra

scoped instance targetResidueAlgebra (x : X) :
    Algebra (TargetStalk x) (PointField x) := (residueHom x).toAlgebra

scoped instance sourceResidueAlgebra (f : X ⟶ X) (x : X) :
    Algebra (SourceStalk f x) (PointField x) := (sourceCoeffHom f x).toAlgebra

scoped instance baseResidueAlgebra (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    Algebra (BaseStalk p f x) (PointField x) := (baseCoeffHom p f x).toAlgebra

open scoped H101DirectFieldRoute.ActualTransport

scoped instance baseSourceTargetTower (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    IsScalarTower (BaseStalk p f x) (SourceStalk f x) (TargetStalk x) :=
  IsScalarTower.of_algebraMap_eq' (by rfl)

scoped instance sourceTargetResidueTower (f : X ⟶ X) (x : X) :
    IsScalarTower (SourceStalk f x) (TargetStalk x) (PointField x) :=
  IsScalarTower.of_algebraMap_eq' (by rfl)

scoped instance baseTargetResidueTower (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    IsScalarTower (BaseStalk p f x) (TargetStalk x) (PointField x) :=
  IsScalarTower.of_algebraMap_eq' (by rfl)

scoped instance baseSourceResidueTower (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    IsScalarTower (BaseStalk p f x) (SourceStalk f x) (PointField x) :=
  IsScalarTower.of_algebraMap_eq' (by ext r; rfl)

/-- The actual source/target tangent base points agree because f is over B. -/
def basePointEq (p : X ⟶ B) (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    p (f x) = p x := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : X ⟶ B => q x) hbase

/-- The canonical base-stalk isomorphism; no chosen replacement base ring. -/
def baseStalkIso (p : X ⟶ B) (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    B.presheaf.stalk (p (f x)) ≅ B.presheaf.stalk (p x) :=
  B.presheaf.stalkCongr (.of_eq (basePointEq p f x hbase))

/-- The actual composed base map, compared with p.stalkMap x through the
canonical base-stalk iso. This is a proved square, not an input Fact. -/
theorem baseComposite_square (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) :
    p.stalkMap (f x) ≫ f.stalkMap x =
      (baseStalkIso p f x hbase).hom ≫ p.stalkMap x := by
  rw [← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom (f ≫ p) p hbase x

theorem baseComposite_apply (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) (r : BaseStalk p f x) :
    baseTargetHom p f x r = p.stalkMap x ((baseStalkIso p f x hbase).hom r) :=
  congrArg (fun q : B.presheaf.stalk (p (f x)) ⟶ X.presheaf.stalk x => q r)
    (baseComposite_square p f x hbase)

theorem baseComposite_inv_apply (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) (r : B.presheaf.stalk (p x)) :
    baseTargetHom p f x ((baseStalkIso p f x hbase).inv r) = p.stalkMap x r := by
  rw [baseComposite_apply p f x hbase]
  exact congrArg (fun v => p.stalkMap x v)
    ((baseStalkIso p f x hbase).commRingCatIsoToRingEquiv.apply_symm_apply r)

/-- The actual residue square for f.stalkMap x. -/
theorem residueSquare_apply (f : X ⟶ X) (x : X) (a : SourceStalk f x) :
    (f.residueFieldMap x).hom (residueHom (f x) a) = sourceCoeffHom f x a :=
  congrArg (fun q : X.presheaf.stalk (f x) ⟶ X.residueField x => q a)
    (Scheme.residue_residueFieldMap f x)

/-- The actual coefficient isomorphism, linear over the actual source stalk.
Its linearity is the native residue square, not an assumed compatibility. -/
def coefficientIso (f : X ⟶ X) (x : X) [IsIso (f.residueFieldMap x)] :
    PointField (f x) ≃ₗ[SourceStalk f x] PointField x where
  __ := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.toAddEquiv
  map_smul' a r := by
    change (f.residueFieldMap x).hom (residueHom (f x) a * r) =
      sourceCoeffHom f x a * (f.residueFieldMap x).hom r
    rw [map_mul, residueSquare_apply]

@[simp]
theorem coefficientIso_apply (f : X ⟶ X) (x : X) [IsIso (f.residueFieldMap x)]
    (r : PointField (f x)) :
    coefficientIso f x r = (f.residueFieldMap x).hom r := rfl

end H101DirectFieldRoute.ActualTransport
