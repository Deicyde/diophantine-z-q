import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtProductKernelV2
import ZInQKernel.Contrib.OneProof.EllAdic.FiniteResidueSubShiftV1
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u v

private noncomputable def productSectionCoordinates {C : Type*} [Category C]
    (E : C ⥤ Type v) (F : ℕ → C) [HasProduct F]
    [PreservesLimit (Discrete.functor F) E] :
    E.obj (∏ᶜ F) ≅ ((n : ℕ) → E.obj (F n)) :=
  PreservesProduct.iso E F ≪≫ Types.productIso _

private lemma productSectionCoordinates_hom_apply {C : Type*} [Category C]
    (E : C ⥤ Type v) (F : ℕ → C) [HasProduct F]
    [PreservesLimit (Discrete.functor F) E] (x : E.obj (∏ᶜ F)) (n : ℕ) :
    ((productSectionCoordinates E F).hom x) n = E.map (Pi.π F n) x := by
  have h : (productSectionCoordinates E F).hom ≫ (↾fun a => a n) = E.map (Pi.π F n) := by
    unfold productSectionCoordinates
    rw [Iso.trans_hom, Category.assoc, Types.productIso_hom_comp_eval,
      PreservesProduct.iso_hom, piComparison_comp_π]
  exact congrArg (fun a : E.obj (∏ᶜ F) ⟶ E.obj (F n) => a x) h

private abbrev residueUnderlyingSections (S : Scheme.{u}) (U : (S.ProEt)ᵒᵖ) :
    Sheaf (Scheme.ProEt.topology S) Ab.{u+1} ⥤ Type (u + 1) :=
  sheafToPresheaf (Scheme.ProEt.topology S) Ab.{u+1} ⋙
    (evaluation ((S.ProEt)ᵒᵖ) Ab.{u+1}).obj U ⋙ forget Ab.{u+1}

/-- The product difference is surjective on each object: choose the next
locally constant residue section using the literal finite reduction. -/
theorem finiteResidueProEtSubShift_sections_surjective (S : Scheme.{u}) (p : ℕ)
    (U : (S.ProEt)ᵒᵖ) :
    Function.Surjective ((finiteResidueProEtSubShift S p).hom.app U) := by
  let T := liftedFiniteResidueProEtSheafTower S p
  let F := towerObjects T
  let E := residueUnderlyingSections S U
  change Function.Surjective (E.map (finiteResidueProEtSubShift S p))
  let e := productSectionCoordinates E F
  let A (n : ℕ) : Ab.{u+1} := (F n).obj.obj U
  let step (n : ℕ) : A (n + 1) →+ A n :=
    ((T.map (homOfLE (Nat.le_succ n)).op).hom.app U).hom
  have hs (n : ℕ) : Function.Surjective (step n) := by
    intro y
    change ULift.{u+1} (LocallyConstant U.unop.left (ZMod (p ^ n))) at y
    obtain ⟨z, hz⟩ := locallyConstantResidueReduction_surjective p (Nat.le_succ n) U.unop.left y.down
    exact ⟨⟨z⟩, ULift.ext hz⟩
  intro y
  obtain ⟨a, ha⟩ := sequenceSubShift_surjective (A := fun n => A n) step hs
    (show ∀ n, A n from e.hom y)
  let x := e.inv a
  refine ⟨x, ?_⟩
  have hx : e.hom x = a := by
    exact congrArg (fun f : ((n : ℕ) → E.obj (F n)) ⟶ ((n : ℕ) → E.obj (F n)) => f a)
      e.inv_hom_id
  have hxy : e.hom (E.map (finiteResidueProEtSubShift S p) x) = e.hom y := by
    funext n
    have hδ := congrArg (fun f : (∏ᶜ F) ⟶ F n => E.map f x) (towerSubShift_π T n)
    change E.map (finiteResidueProEtSubShift S p ≫ Pi.π F n) x =
      (show A n from E.map (Pi.π F n) x) - step n (E.map (Pi.π F (n + 1)) x) at hδ
    rw [E.map_comp, types_comp_apply] at hδ
    change ((productSectionCoordinates E F).hom (E.map (finiteResidueProEtSubShift S p) x)) n = _
    rw [productSectionCoordinates_hom_apply, hδ, ← productSectionCoordinates_hom_apply,
      ← productSectionCoordinates_hom_apply]
    change (show A n from (e.hom x) n) - step n ((e.hom x) (n + 1)) = (e.hom y) n
    rw [hx]
    exact congrFun ha n
  have hinv (z : E.obj (∏ᶜ F)) : e.inv (e.hom z) = z :=
    congrArg (fun f : E.obj (∏ᶜ F) ⟶ E.obj (∏ᶜ F) => f z) e.hom_inv_id
  exact (hinv _).symm.trans (congrArg (fun r => e.inv r) hxy |>.trans (hinv _))

/-- A sectionwise-surjective difference morphism is an epimorphism of these
actual sheaves. This does not assert exact products of arbitrary sheaf epis. -/
theorem finiteResidueProEtSubShift_epi (S : Scheme.{u}) (p : ℕ) :
    Epi (finiteResidueProEtSubShift S p) := by
  let : Sheaf.IsLocallySurjective (finiteResidueProEtSubShift S p) :=
    Presheaf.isLocallySurjective_of_surjective (Scheme.ProEt.topology S) _
      (finiteResidueProEtSubShift_sections_surjective S p)
  infer_instance

end RC53.EllAdic
