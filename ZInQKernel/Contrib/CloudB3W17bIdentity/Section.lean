import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.OkaAdapter
import ZInQKernel.HDecomp.LeafPush2.R22

/-!
# The actual identity section of an original abelian variety in Oka's scheme category

For the ORIGINAL `B : PkgI3.AbVar ℂ`, the unit `η[B.X] : 𝟙_ ⟶ B.X` of its group object over
`Spec ℂ` is transported, without changing any underlying scheme or scheme morphism, into Oka's
category `ComplexAnalytic.SchemeLFTℂ` of schemes locally of finite type over
`Spec (ULift ℂ)`. Only the structure morphisms are re-spelled along the genuine base isomorphism
`complexULiftBaseIso` (literally `Spec.map` of `ULift.ringEquiv`).

The resulting morphism `identitySection B` is a closed immersion because it is a section of the
separated structure morphism of the proper scheme `B.X` (Mathlib's
`AlgebraicGeometry.IsClosedImmersion.of_comp`); no closedness, algebraicity or comparison
hypothesis is added. Its image is exactly the closed point of the original identity, which is
the point underlying the identity element `1` of the kernel's group of complex points.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.CloudB3W17bOkaComparison ZInQ.Contrib.CloudB3W17bProjectiveBridge

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bIdentity

/-- The native monoidal unit of schemes over `Spec ℂ`: the actual source of `η[B.X]`. -/
abbrev nativeUnit : Over (Spec (CommRingCat.of ℂ)) := 𝟙_ (Over (Spec (CommRingCat.of ℂ)))

theorem nativeUnit_hom : nativeUnit.hom = 𝟙 (Spec (CommRingCat.of ℂ)) := rfl

theorem nativeUnit_left : nativeUnit.left = Spec (CommRingCat.of ℂ) := rfl

instance nativeUnit_locallyOfFiniteType : LocallyOfFiniteType nativeUnit.hom :=
  (inferInstance : LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of ℂ))))

/-- The native unit, with only its base spelled over Oka's lifted complex base. -/
def unitLiftedLFT : ComplexAnalytic.SchemeLFTℂ.{0} :=
  ⟨overULift nativeUnit, show LocallyOfFiniteType (overULift nativeUnit).hom from inferInstance⟩

@[simp]
theorem unitLiftedLFT_left : unitLiftedLFT.obj.left = Spec (CommRingCat.of ℂ) := rfl

theorem unitLiftedLFT_hom : unitLiftedLFT.obj.hom = nativeUnit.hom ≫ complexULiftBaseIso.hom :=
  rfl

/-- The unit's structure morphism is literally the genuine base isomorphism. -/
theorem unitLiftedLFT_hom_eq_baseIso : unitLiftedLFT.obj.hom = complexULiftBaseIso.hom :=
  Category.id_comp _

/-- **The actual identity section of the original `B`** in Oka's scheme category. -/
def identitySection (B : PkgI3.AbVar ℂ) : unitLiftedLFT ⟶ abVarLiftedLFT B :=
  ObjectProperty.homMk (overULiftMap η[B.X])

/-- The underlying scheme morphism is literally the original unit `η[B.X].left`. -/
@[simp]
theorem identitySection_hom_left (B : PkgI3.AbVar ℂ) :
    (identitySection B).hom.left = η[B.X].left := rfl

/-- The original unit is a section of the original structure morphism. -/
theorem eta_left_comp_hom (B : PkgI3.AbVar ℂ) :
    η[B.X].left ≫ B.X.hom = 𝟙 (Spec (CommRingCat.of ℂ)) :=
  Over.w η[B.X]

/-- The section is over Oka's actual base, with the genuine base isomorphism. -/
theorem identitySection_over (B : PkgI3.AbVar ℂ) :
    (identitySection B).hom.left ≫ (abVarLiftedLFT B).obj.hom = complexULiftBaseIso.hom := by
  change η[B.X].left ≫ (B.X.hom ≫ complexULiftBaseIso.hom) = complexULiftBaseIso.hom
  rw [← Category.assoc, eta_left_comp_hom]
  exact Category.id_comp _

/-- The original unit is a closed immersion: a section of the separated morphism `B.X.hom`. -/
instance isClosedImmersion_eta_left (B : PkgI3.AbVar ℂ) : IsClosedImmersion η[B.X].left := by
  have : IsClosedImmersion (η[B.X].left ≫ B.X.hom) := by
    rw [eta_left_comp_hom]
    exact (inferInstance : IsClosedImmersion (𝟙 (Spec (CommRingCat.of ℂ))))
  exact IsClosedImmersion.of_comp η[B.X].left B.X.hom

/-- **The actual identity section is a closed immersion.** -/
instance isClosedImmersion_identitySection (B : PkgI3.AbVar ℂ) :
    IsClosedImmersion (identitySection B).hom.left :=
  isClosedImmersion_eta_left B

/-- The closed scheme point of the original identity of `B`. -/
def identityPoint (B : PkgI3.AbVar ℂ) : B.X.left :=
  η[B.X].left (IsLocalRing.closedPoint ℂ)

/-- **The image of the identity section is exactly the original identity point.** -/
theorem range_identitySection (B : PkgI3.AbVar ℂ) :
    Set.range (identitySection B).hom.left.base = {identityPoint B} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change η[B.X].left p = η[B.X].left (IsLocalRing.closedPoint ℂ)
    congr 1
    exact Subsingleton.elim (α := Spec (CommRingCat.of ℂ)) _ _
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint ℂ, rfl⟩

/-- The identity element of the kernel's group `B(ℂ) = CPts B id` is literally `toUnit ≫ η`,
i.e. it factors through the identity section. -/
theorem cpts_one_eq (B : PkgI3.AbVar ℂ) :
    (1 : ZInQ.LeafPush2.CPts B (RingHom.id ℂ)) =
      toUnit (ZInQ.LeafPush2.cptObj (RingHom.id ℂ)) ≫ η[B.X] := rfl

/-- **The point underlying the kernel's identity element `1 ∈ CPts B id` is `identityPoint B`.** -/
theorem cpts_one_left_closedPoint (B : PkgI3.AbVar ℂ) :
    (1 : ZInQ.LeafPush2.CPts B (RingHom.id ℂ)).left (IsLocalRing.closedPoint ℂ) =
      identityPoint B := by
  change η[B.X].left ((toUnit (ZInQ.LeafPush2.cptObj (RingHom.id ℂ))).left
    (IsLocalRing.closedPoint ℂ)) = η[B.X].left (IsLocalRing.closedPoint ℂ)
  congr 1

/-- The same for the kernel's group of `ℂ`-points `B.Pt ℂ`. -/
theorem pt_one_left_closedPoint (B : PkgI3.AbVar ℂ) :
    (1 : B.Pt ℂ).left (IsLocalRing.closedPoint ℂ) = identityPoint B := by
  change η[B.X].left ((toUnit (PkgI3.AbVar.ptObj (K := ℂ) ℂ)).left
    (IsLocalRing.closedPoint ℂ)) = η[B.X].left (IsLocalRing.closedPoint ℂ)
  congr 1

/-- The image of the identity section is the point of the kernel's identity element. -/
theorem range_identitySection_eq_one (B : PkgI3.AbVar ℂ) :
    Set.range (identitySection B).hom.left.base =
      {(1 : ZInQ.LeafPush2.CPts B (RingHom.id ℂ)).left (IsLocalRing.closedPoint ℂ)} := by
  rw [cpts_one_left_closedPoint, range_identitySection]

end ZInQ.Contrib.CloudB3W17bIdentity
