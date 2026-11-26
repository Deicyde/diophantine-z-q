import ZInQKernel.Contrib.OneProof.EllAdic.PadicResidueCoherenceV1
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.LocallyConstant.Algebra

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- Reduction between the actual locally constant finite residue sections. -/
def locallyConstantResidueReduction (p : ℕ) {m n : ℕ} (h : m ≤ n)
    (U : Type*) [TopologicalSpace U] : LocallyConstant U (ZMod (p ^ n)) →+
      LocallyConstant U (ZMod (p ^ m)) where
  toFun r := ⟨fun x => padicResidueProjection p h (r x),
    r.isLocallyConstant.comp (padicResidueProjection p h)⟩
  map_zero' := by
    apply LocallyConstant.ext
    intro x
    change padicResidueProjection p h 0 = 0
    exact map_zero _
  map_add' r s := by
    apply LocallyConstant.ext
    intro x
    change padicResidueProjection p h (r x + s x) =
      padicResidueProjection p h (r x) + padicResidueProjection p h (s x)
    exact map_add _ _ _

lemma locallyConstantResidueReduction_surjective (p : ℕ) {m n : ℕ} (h : m ≤ n)
    (U : Type*) [TopologicalSpace U] :
    Function.Surjective (locallyConstantResidueReduction p h U) := by
  intro r
  obtain ⟨s, hs, hred⟩ := locallyConstantResidue_lift p h (fun x => r x) r.isLocallyConstant
  refine ⟨⟨s, hs⟩, ?_⟩
  apply LocallyConstant.ext
  exact hred

/-- The actual finite-residue coefficient sections, with restriction given by
precomposition on the underlying topological spaces. -/
def finiteResidueSchemePresheaf (p n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop (ZMod (p ^ n)))
  map f := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom f.unop.base.hom)
  map_id _ := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro r
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro r
    apply LocallyConstant.ext
    intro x
    rfl

/-- Reduction is natural because it acts on the values of sections and
restriction acts on their arguments. -/
def finiteResidueSchemeTransition (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    finiteResidueSchemePresheaf.{u} p n ⟶ finiteResidueSchemePresheaf p m where
  app U := AddCommGrpCat.ofHom (locallyConstantResidueReduction p h U.unop)
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro r
    apply LocallyConstant.ext
    intro x
    rfl

lemma finiteResidueSchemeTransition_refl (p n : ℕ) :
    finiteResidueSchemeTransition.{u} p (le_refl n) = 𝟙 (finiteResidueSchemePresheaf p n) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext
  intro r
  change LocallyConstant U.unop (ZMod (p ^ n)) at r
  apply LocallyConstant.ext
  intro x
  change padicResidueProjection p (le_refl n) (r x) = r x
  simp only [padicResidueProjection_refl, RingHom.id_apply]

lemma finiteResidueSchemeTransition_comp (p : ℕ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    finiteResidueSchemeTransition.{u} p hnk ≫ finiteResidueSchemeTransition p hmn =
      finiteResidueSchemeTransition p (hmn.trans hnk) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext
  intro r
  change LocallyConstant U.unop (ZMod (p ^ k)) at r
  apply LocallyConstant.ext
  intro x
  change padicResidueProjection p hmn (padicResidueProjection p hnk (r x)) =
    padicResidueProjection p (hmn.trans hnk) (r x)
  exact congrArg (fun a : ZMod (p ^ k) →+* ZMod (p ^ m) => a (r x))
    (padicResidueProjection_comp p hmn hnk)

/-- The actual indexing category for the finite coefficient presheaves. -/
def finiteResidueSchemeTower (p : ℕ) : ℕᵒᵖ ⥤ (Scheme.{u}ᵒᵖ ⥤ Ab.{u}) where
  obj n := finiteResidueSchemePresheaf p n.unop
  map f := finiteResidueSchemeTransition p (leOfHom f.unop)
  map_id n := finiteResidueSchemeTransition_refl p n.unop
  map_comp f g := (finiteResidueSchemeTransition_comp p (leOfHom g.unop) (leOfHom f.unop)).symm

end RC53.EllAdic
