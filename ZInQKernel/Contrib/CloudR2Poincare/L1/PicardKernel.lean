import ZInQKernel.Contrib.CloudR2Poincare.L1.PolarizationFamily
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RationalPoint
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field

/-!
# The polarization classifier's kernel is the line-bundle stabilizer

H-72 round 2, L1. The important issue here is **after sheafification**:
`toPicardFunctor` need not be injective over arbitrary parameter schemes because
classes pulled back from the parameter are killed. For a parameter with trivial
Picard group (in particular Spec Ω for every field Ω), proper geometric
integrality and a rational section make it injective. Hence the kernel of the
actual representing morphism is exactly the translation stabilizer on points.

No representability or dual-existence Fact is installed. A supplied representing
correspondence remains an explicit argument to the conditional classifier API.
The injectivity and class/stabilizer identities themselves do not assume any
representing scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- Pullback on Picard classes along an isomorphism is injective. -/
theorem pic_map_injective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Injective (Pic.map f) := by
  intro L M h
  have e := congrArg (Pic.map (inv f)) h
  simpa only [← Pic.map_comp, IsIso.inv_hom_id, Pic.map_id] using e

/-- The Picard sheaf unit is injective on a test scheme with trivial Picard group. -/
theorem toPicardFunctor_injective_of_subsingletonPic
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (T : Over (Spec (.of k))) [Subsingleton T.left.Pic] :
    Function.Injective ((toPicardFunctor f).app (.op T)) := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : IsProper (X ↘ Spec (.of k)) := by change IsProper f; infer_instance
  haveI : GeometricallyIntegral (X ↘ Spec (.of k)) := by
    change GeometricallyIntegral f
    infer_instance
  let e : (picardFunctorNormalized f σ hσ).toFunctor ≅ (picardFunctor f).obj :=
    normalizedPicardIso (source := X) σ hσ
  intro L M h
  have hL : L ∈ (picardFunctorNormalized f σ hσ).obj (.op T) := by
    change Pic.map _ L = 1
    exact Subsingleton.elim _ _
  have hM : M ∈ (picardFunctorNormalized f σ hσ).obj (.op T) := by
    change Pic.map _ M = 1
    exact Subsingleton.elim _ _
  let L' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) := ⟨L, hL⟩
  let M' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) := ⟨M, hM⟩
  have he : e.hom.app (.op T) L' = e.hom.app (.op T) M' := by
    rw [show e.hom = (picardFunctorNormalized f σ hσ).ι ≫ toPicardFunctor f from
      normalizedPicardIso_hom σ hσ]
    exact h
  have hinj : Function.Injective (e.hom.app (.op T)) :=
    Function.LeftInverse.injective (g := e.inv.app (.op T)) (by
      intro z
      exact ConcreteCategory.congr_hom (e.hom_inv_id_app (.op T)) z)
  exact congrArg Subtype.val (hinj he)

/-- In particular the unit is injective on every field-valued test scheme. -/
theorem toPicardFunctor_injective_field
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    Function.Injective ((toPicardFunctor f).app
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))) := by
  haveI : Subsingleton (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of Ω)).Pic)
  exact toPicardFunctor_injective_of_subsingletonPic f σ hσ _

/-- The translation stabilizer on rational points, stated using actual bundle classes. -/
def translationStabilizer {S : Scheme.{u}} (A : Over S) [MonObj A] (L : A.left.Pic) :
    Set (𝟙_ (Over S) ⟶ A) :=
  {x | Pic.map (translate A x).left L = L}

/-- Kernel identification after Picard sheafification on a field-like test scheme. -/
theorem polarizationMorphism_kernel_family
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
    [IsProper A.hom] [GeometricallyIntegral A.hom] (L : A.left.Pic)
    {P T : Over (Spec (.of k))} [Subsingleton T.left.Pic]
    (representation : (picardFunctor A.hom).obj.RepresentableBy P) (x : T ⟶ A) :
    letI := picardFunctorCommGrpObj A.hom representation
    x ≫ polarizationMorphism A L representation = 1 ↔ polarizationFamily A L x = 1 := by
  letI := picardFunctorCommGrpObj A.hom representation
  have hσ : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have unit_inj := toPicardFunctor_injective_of_subsingletonPic A.hom η[A].left hσ T
  have classifier_one := (picardClassifyingHom A.hom representation T).map_one
  have one_classifies : (toPicardFunctor A.hom).app (.op T)
      (1 : (pullback A.hom T.hom).Pic) = representation.homEquiv (1 : T ⟶ P) := by
    have := congrArg representation.homEquiv classifier_one
    simpa only [picardClassifyingHom_apply, Equiv.apply_symm_apply] using this
  constructor
  · intro h
    apply unit_inj
    rw [← polarizationMorphism_classifies, h]
    exact one_classifies.symm
  · intro h
    apply representation.homEquiv.injective
    rw [polarizationMorphism_classifies, h]
    exact one_classifies

/-- For rational points, the actual classifier kernel is exactly `K(L)`. -/
theorem polarizationMorphism_kernel_rationalPoint
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
    [IsProper A.hom] [GeometricallyIntegral A.hom] (L : A.left.Pic)
    {P : Over (Spec (.of k))}
    (representation : (picardFunctor A.hom).obj.RepresentableBy P)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    letI := picardFunctorCommGrpObj A.hom representation
    x ≫ polarizationMorphism A L representation = 1 ↔
      Pic.map (translate A x).left L = L := by
  letI := picardFunctorCommGrpObj A.hom representation
  haveI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
  rw [polarizationMorphism_kernel_family]
  have section_eq : lift (𝟙 A) (toUnit A) = (ρ_ A).inv := by
    ext <;> simp
  haveI : IsIso (lift (𝟙 A) (toUnit A)).left := by
    rw [section_eq]
    infer_instance
  have hinj := pic_map_injective_of_isIso (lift (𝟙 A) (toUnit A)).left
  have hclass := polarizationFamily_rationalPoint A L x
  rw [← translationClass_eq_one_iff A L x, ← hclass]
  exact ⟨fun h ↦ by rw [h, Pic.map_one], fun h ↦ hinj (h.trans (Pic.map_one _).symm)⟩

/-- Equality of sets, in the form used by the finite-geometric-kernel lane. -/
theorem polarizationMorphism_kernel_eq_stabilizer
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
    [IsProper A.hom] [GeometricallyIntegral A.hom] (L : A.left.Pic)
    {P : Over (Spec (.of k))}
    (representation : (picardFunctor A.hom).obj.RepresentableBy P) :
    letI := picardFunctorCommGrpObj A.hom representation
    {x : 𝟙_ (Over (Spec (.of k))) ⟶ A |
      x ≫ polarizationMorphism A L representation = 1} = translationStabilizer A L := by
  letI := picardFunctorCommGrpObj A.hom representation
  ext x
  exact polarizationMorphism_kernel_rationalPoint A L representation x

end ZInQ.Contrib.CloudR2Poincare.L1
