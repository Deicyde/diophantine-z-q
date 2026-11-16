import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.Contrib.CloudW03NeronSurj.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# D5: retain the kernel group law and its actual sections

Original dictionary glue, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The group-law conversion is the canonical, already public H76 construction
(from the Apache-2.0 Anthropic FLT development; see that module's licence notice).
No group law, quaternion action, or level point is chosen anew.
-/

set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 LeafQM
open ZInQ.Contrib.CloudW03NeronSurj.FLT
open NeronModelInfra GoodReductionJacobian

variable {K : Type} [Field K]

/-- The original kernel group object, read as the canonical relative group law. -/
def kernelLaw (A : AbVar K) : RelativeGroupLaw K A.X.hom :=
  letI : GrpObj (Over.mk A.X.hom) := A.grp
  relativeGroupLawOfGrpObj K A.X.hom

/-- The unique field fibre is the entire actual carrier. -/
theorem kernelFibre_univ (A : AbVar K) (s : Spec (CommRingCat.of K)) :
    A.X.hom.base ⁻¹' {s} = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

/-- The original surface dimension on the original carrier, at each field fibre. -/
theorem kernel_dim_fibre (P : AV.QML3 K) (s : Spec (CommRingCat.of K)) :
    topologicalKrullDim ↥(P.A.X.hom.base ⁻¹' {s}) = 2 := by
  rw [kernelFibre_univ]
  exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ P.A.X.left)
    (Homeomorph.Set.univ P.A.X.left).isHomeomorph).trans P.surface

/-- The abelian variety's own relative law is commutative. -/
theorem kernelLaw_comm (A : AbVar K) : (kernelLaw A).IsCommutative := by
  intro T t x y
  letI : GrpObj (Over.mk A.X.hom) := A.grp
  haveI : IsProper (Over.mk A.X.hom).hom := A.proper
  haveI : GeometricallyIntegral (Over.mk A.X.hom).hom := A.geomInt
  haveI : IsCommMonObj (Over.mk A.X.hom) :=
    isCommMonObj_of_isProper_of_geometricallyIntegral (Over.mk A.X.hom)
  haveI := (isCommMonObj_iff_isMulCommutative (Over.mk A.X.hom)).mp
    inferInstance (Over.mk t)
  change overHomToSchemeHomOver
      (schemeHomOverToOverHom x * schemeHomOverToOverHom y) =
    overHomToSchemeHomOver (schemeHomOverToOverHom y * schemeHomOverToOverHom x)
  exact congrArg overHomToSchemeHomOver
    (mul_comm (schemeHomOverToOverHom x) (schemeHomOverToOverHom y))

/-- Genuine geometry of the original kernel abelian variety. -/
theorem kernel_bundle (A : AbVar K) : AbelianSchemePropertyBundle K A.X.hom where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres s := by
    haveI : IrreducibleSpace A.X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
    rw [kernelFibre_univ]
    exact isConnected_univ
  hasGroupLaw := ⟨kernelLaw A⟩

/-- A rational point is a section of the original structure morphism. -/
theorem kernelPt_over (A : AbVar K) (x : A.Pt K) : x.left ≫ A.X.hom = 𝟙 _ := by
  rw [Over.w]
  simp [AbVar.ptObj, Algebra.algebraMap_self]

/-- The actual kernel rational point, as a section (unchanged underlying morphism). -/
def kernelPt (A : AbVar K) (x : A.Pt K) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.X.hom :=
  ⟨x.left, kernelPt_over A x⟩

@[simp] theorem kernelPt_coe (A : AbVar K) (x : A.Pt K) :
    (kernelPt A x).1 = x.left := rfl

/-- The kernel's rational-point object has the identity structure map. -/
theorem kernelPtObj_self : (AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
  simp [AbVar.ptObj, Algebra.algebraMap_self]

theorem kernelPt_mul (A : AbVar K) (x y : A.Pt K) :
    kernelPt A (x * y) = (kernelLaw A).mul (𝟙 _) (kernelPt A x) (kernelPt A y) := by
  rcases A with ⟨⟨X, ⟨⟨⟩⟩, f⟩, grp, hp, hs, hi⟩
  apply Subtype.ext
  simp only [kernelPt, kernelLaw, relativeGroupLawOfGrpObj,
    overHomToSchemeHomOver, schemeHomOverToOverHom, Hom.mul_def,
    Over.comp_left, Over.lift_left, Over.homMk_left]
  dsimp only [AbVar.ptObj, Over.mk_left] at x y ⊢
  congr 1

theorem kernelPt_one (A : AbVar K) : kernelPt A 1 = (kernelLaw A).one (𝟙 _) := by
  letI : GrpObj (Over.mk A.X.hom) := A.grp
  apply Subtype.ext
  change (AbVar.ptObj (K := K) K).hom ≫ η[A.X].left =
    (𝟙 (Spec (CommRingCat.of K))) ≫ η[A.X].left
  rw [kernelPtObj_self]
  dsimp only [AbVar.ptObj, Over.mk_left]

/-- Identity section for the `N=1` subgroup; this is not a new point. -/
def kernelIdentity (A : AbVar K) : Spec (CommRingCat.of K) ⟶ A.X.left :=
  ((kernelLaw A).one (𝟙 _)).1

theorem kernelIdentity_over (A : AbVar K) : kernelIdentity A ≫ A.X.hom = 𝟙 _ :=
  ((kernelLaw A).one (𝟙 _)).2

/-- The actual identity section is a closed immersion over the one-point field spectrum. -/
theorem kernelIdentity_closed (A : AbVar K) : IsClosedImmersion (kernelIdentity A) :=
  isClosedImmersion_of_comp_eq_id A.X.hom (kernelIdentity A) (kernelIdentity_over A)

/-- Factoring through the identity section means literally being the identity point. -/
theorem factors_kernelIdentity_iff (A : AbVar K) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t A.X.hom) :
    (∃ z : T ⟶ Spec (CommRingCat.of K), z ≫ kernelIdentity A = x.1) ↔
      x = (kernelLaw A).one t := by
  constructor
  · rintro ⟨z, hz⟩
    have hzt : z = t := by
      have he := congrArg (fun v => v ≫ A.X.hom) hz
      simpa only [Category.assoc, kernelIdentity_over, Category.comp_id, x.2] using he
    subst z
    apply Subtype.ext
    have hone := congrArg Subtype.val ((kernelLaw A).one_natural (𝟙 _) t t (Category.comp_id _))
    exact hz.symm.trans hone
  · rintro rfl
    refine ⟨t, ?_⟩
    exact congrArg Subtype.val ((kernelLaw A).one_natural (𝟙 _) t t (Category.comp_id _))

/-- Every endomorphism of the original abelian variety fixes its own identity point. -/
theorem kernelEnd_one (A : AbVar K) (phi : AbVar.End A) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    ((kernelLaw A).one t).1 ≫ phi.hom.left = ((kernelLaw A).one t).1 := by
  letI : GrpObj (Over.mk A.X.hom) := A.grp
  have h : (1 : Over.mk t ⟶ A.X) ≫ phi.hom = 1 := MonObj.one_comp _
  exact congrArg CommaMorphism.left h

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
