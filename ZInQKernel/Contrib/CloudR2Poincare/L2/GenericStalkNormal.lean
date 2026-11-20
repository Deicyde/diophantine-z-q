import ZInQKernel.Contrib.CloudR2Poincare.L2.GeometricProjection
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Generic stalk isomorphism and the finite birational/normal endpoint

Geometric point bijectivity gives original finite/surjective/radicial p and
source integrality. Radicial residue extensions are trivial in char zero,
so the ACTUAL generic stalk map is an isomorphism. The remaining target
normality premise is stated explicitly in the intermediate affine lemma.
It is not installed as a Fact or silently inferred from dimension-one normality.

The affine integral-closure argument is adapted from AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/BirationalIsIso.lean
lines42–97 (Apache-2.0). Change notice: use the actual generic-stalk iso and
explicit affine integrally-closed hypothesis instead of importing upstream
IsNormal/IsBirational structures and their large closure. No desired leaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Original projection homeomorphism carries the ACTUAL generic point to
J's generic point. No B→Γ surjectivity statement is used. -/
theorem genericPoint_map_of_geometricFieldPoint_bijective
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced G.left]
    (p : G ⟶ J.X) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p)) :
    letI : IsIntegral G.left := isIntegral_source_of_geometricFieldPoint_bijective J G p hp
    letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
    p.left (genericPoint G.left) = genericPoint J.X.left := by
  letI : IsIntegral G.left := isIntegral_source_of_geometricFieldPoint_bijective J G p hp
  letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  have h := isHomeomorph_of_geometricFieldPoint_bijective p hp
  apply ((genericPoint_spec J.X.left).eq _).symm
  simpa only [Set.image_univ, h.bijective.surjective.range_eq, closure_univ] using
    (genericPoint_spec G.left).image p.left.continuous

/-- The ACTUAL generic stalk map is an iso: both generic stalks are fields,
so the char-zero radicial residue isomorphism detects the stalk isomorphism. -/
theorem isIso_genericStalkMap_of_geometricFieldPoint_bijective
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced G.left]
    (p : G ⟶ J.X) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p)) :
    letI : IsIntegral G.left := isIntegral_source_of_geometricFieldPoint_bijective J G p hp
    IsIso (p.left.stalkMap (genericPoint G.left)) := by
  letI : IsIntegral G.left := isIntegral_source_of_geometricFieldPoint_bijective J G p hp
  letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  have hgen := genericPoint_map_of_geometricFieldPoint_bijective J G p hp
  have hinj : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Injective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p) := by
    intro Ω _ _ _ _ a b h
    exact (hp Ω).1 h
  letI : UniversallyInjective p.left := universallyInjective_of_geometricFieldPoints p hinj
  let g := genericPoint G.left
  have hfield : IsField (J.X.left.presheaf.stalk (p.left g)) := by
    rw [show p.left g = genericPoint J.X.left from hgen]
    exact Field.toIsField J.X.left.functionField
  letI : Field (J.X.left.presheaf.stalk (p.left g)) := hfield.toField
  letI : IsIso (J.X.left.residue (p.left g)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(J.X.left.residue (p.left g)).hom.injective, Scheme.residue_surjective _ _⟩
  letI : IsIso (G.left.residue g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(G.left.residue g).hom.injective, Scheme.residue_surjective _ _⟩
  letI : IsIso (p.left.residueFieldMap g) :=
    isIso_residueFieldMap_of_universallyInjective_charZero p g
  have hs : p.left.stalkMap g = J.X.left.residue (p.left g) ≫
      p.left.residueFieldMap g ≫ inv (G.left.residue g) := by
    apply (cancel_mono (G.left.residue g)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Scheme.residue_residueFieldMap p.left g).symm
  rw [hs]
  infer_instance

private theorem isFractionRing_stalk_of_eq_genericPoint
    (Y : Scheme.{u}) [IsIntegral Y] (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (x : Y) (hxU : x ∈ U) (hx : x = genericPoint Y) :
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk x) := (Y.presheaf.germ U x hxU).hom.toAlgebra
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk x) := by
  subst x
  exact functionField_isFractionRing_of_isAffineOpen Y U hU

/-- Actual integral-closure endpoint over ONE nonempty affine open. Target
normality remains an explicit intermediate hypothesis, not a supplied final leaf. -/
theorem isIso_app_of_integral_genericStalk_iso_normal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsIntegralHom f]
    (hgen : f (genericPoint X) = genericPoint Y)
    [IsIso (f.stalkMap (genericPoint X))]
    (U : Y.affineOpens) [Nonempty U.1] [IsIntegrallyClosed Γ(Y, U.1)] :
    IsIso (f.app U.1) := by
  have hfxU : f (genericPoint X) ∈ U.1 := by
    rw [hgen]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).2 (by simpa using ‹Nonempty U.1›)
  letI : Nonempty (f ⁻¹ᵁ U.1) := ⟨⟨genericPoint X, hfxU⟩⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply germ_injective_of_isIntegral Y (f (genericPoint X)) hfxU
    apply (ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))).1
    rw [f.germ_stalkMap_apply, f.germ_stalkMap_apply, hab]
  · intro b
    let A := Γ(Y, U.1)
    let B := Γ(X, f ⁻¹ᵁ U.1)
    let KY := Y.presheaf.stalk (f (genericPoint X))
    let KX := X.functionField
    letI : Algebra A B := (f.app U.1).hom.toAlgebra
    letI : Algebra A KX := (f.app U.1 ≫ X.germToFunctionField (f ⁻¹ᵁ U.1)).hom.toAlgebra
    letI : Algebra A KY := (Y.presheaf.germ U.1 (f (genericPoint X)) hfxU).hom.toAlgebra
    letI : IsFractionRing A KY := isFractionRing_stalk_of_eq_genericPoint Y U.1 U.2 _ hfxU hgen
    let e : KY ≃ₐ[A] KX :=
      { (asIso (f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv with
        commutes' := fun a => by
          change f.stalkMap (genericPoint X) (Y.presheaf.germ U.1 (f (genericPoint X)) hfxU a) =
            X.germToFunctionField (f ⁻¹ᵁ U.1) (f.app U.1 a)
          exact f.germ_stalkMap_apply U.1 (genericPoint X) hfxU a }
    letI : IsFractionRing A KX := IsFractionRing.of_algEquiv e
    letI : IsScalarTower A B KX := IsScalarTower.of_algebraMap_eq' rfl
    have hb : _root_.IsIntegral A b := f.isIntegral_app U.1 U.2 b
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff KX).mp
      (inferInstance : IsIntegrallyClosed A) (x := X.germToFunctionField (f ⁻¹ᵁ U.1) b)
      (hb.map (IsScalarTower.toAlgHom A B KX))
    exact ⟨a, X.germToFunctionField_injective (f ⁻¹ᵁ U.1) ha⟩

end ZInQ.Contrib.CloudR2Poincare.L2
