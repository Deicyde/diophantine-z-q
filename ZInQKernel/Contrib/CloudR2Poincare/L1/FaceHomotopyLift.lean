import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Homology.DerivedCategory.KProjective
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Homology.CochainComplex.FlatBaseChange

/-!
# Actual bounded-projective chain lifts with retained homotopies

Layer 3's algebraic lifting primitive. The lift is taken through the ACTUAL
quasi-isomorphism, and equality in the homotopy category is converted to a
stored chain homotopy. Scalar transport maps that SAME homotopy and has no
flatness premise. No dimension/rank-selected equivalence is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- An actual map out of a K-projective complex lifts through an actual
quasi-isomorphism, with an actual retained homotopy witnessing the square. -/
theorem exists_homotopyLift_of_isKProjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P K L : CochainComplex C ℤ} [P.IsKProjective]
    (e : K ⟶ L) [QuasiIso e] (f : P ⟶ L) :
    ∃ g : P ⟶ K, Nonempty (Homotopy (g ≫ e) f) := by
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let ρ := DerivedCategory.quotientCompQhIso C
  have hn : DerivedCategory.Qh.map (Q.map e) ≫ (ρ.app L).hom =
      (ρ.app K).hom ≫ DerivedCategory.Q.map e := by
    simpa only [Q, Iso.app_hom, Functor.comp_map] using ρ.hom.naturality e
  haveI : IsIso (DerivedCategory.Qh.map (Q.map e)) := by
    haveI : IsIso (DerivedCategory.Qh.map (Q.map e) ≫ (ρ.app L).hom) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (ρ.app L).hom
  let desired := DerivedCategory.Qh.map (Q.map f) ≫ inv (DerivedCategory.Qh.map (Q.map e))
  obtain ⟨γ, hγ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (Q.obj K)).surjective desired
  obtain ⟨g, rfl⟩ := Q.map_surjective γ
  have h : Q.map (g ≫ e) = Q.map f := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P (Q.obj L)).injective
    rw [Q.map_comp, Functor.map_comp, hγ]
    simp only [desired, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ h⟩⟩

/-- The native bounded-above projective criterion supplies the lifting property;
no caller-supplied model diagram or homotopy is assumed. -/
theorem exists_homotopyLift_of_bounded_projective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P K L : CochainComplex C ℤ} (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Projective (P.X n)] (e : K ⟶ L) [QuasiIso e] (f : P ⟶ L) :
    ∃ g : P ⟶ K, Nonempty (Homotopy (g ≫ e) f) := by
  haveI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  exact exists_homotopyLift_of_isKProjective e f

/-- The actual retained square homotopy is transported by tensor extension,
including extension to nonflat residue fields. -/
def scalarExtension_faceSquare_homotopy
    {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    {P PX C DX : CochainComplex (ModuleCat.{u} A) ℤ}
    {ψ : P ⟶ PX} {eX : PX ⟶ DX} {eC : P ⟶ C} {Φ : C ⟶ DX}
    (h : Homotopy (ψ ≫ eX) (eC ≫ Φ)) :
    let F := (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)
    Homotopy (F.map ψ ≫ F.map eX) (F.map eC ≫ F.map Φ) := by
  let F := ModuleCat.extendScalars (algebraMap A B)
  simpa only [Functor.map_comp] using F.mapHomotopy h

end ZInQ.Contrib.CloudR2Poincare.L1
