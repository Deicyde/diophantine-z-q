/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq

set_option autoImplicit false

universe u

-- [port] was: p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry"
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry

noncomputable section

namespace FormalGAGAFiniteRelSpecMapAux

-- [port] was: p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite"
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {Y : Scheme.{u}} {F₁ F₂ : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α₁ : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₁}
  {α₂ : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₂}
  (H₁ : α₁.Coequifibered) (H₂ : α₂.Coequifibered) (β : F₂ ⟶ F₁)

scoped instance : ((relativeGluingData H₁).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

lemma cover_f (U : Y.AffineZariskiSite) :
    (relativeGluingData H₁).cover.f U = colimit.ι (relativeGluingData H₁).functor U := by
  simp

def specMap : (relativeGluingData H₁).functor ⟶ (relativeGluingData H₂).functor :=
  Functor.whiskerRight β.rightOp Scheme.Spec

private def _root_.FormalGAGAFiniteRelSpecMapAux.map : (relativeGluingData H₁).glued ⟶ (relativeGluingData H₂).glued :=
  colimMap (specMap H₁ H₂ β)

-- [port] was: p2m_export "FormalGAGAFiniteRelSpecMapAux" "map"
export _root_.FormalGAGAFiniteRelSpecMapAux (map)
@[reassoc]
lemma ι_map (U : Y.AffineZariskiSite) :
    (relativeGluingData H₁).cover.f U ≫ map H₁ H₂ β =
      Spec.map (β.app (op U)) ≫ (relativeGluingData H₂).cover.f U := by
  rw [cover_f, cover_f, map]
  erw [ι_colimMap]
  rfl

lemma ι_toBase (H : α₁.Coequifibered) (U : Y.AffineZariskiSite) :
    (relativeGluingData H).cover.f U ≫ (relativeGluingData H).toBase =
      Spec.map (α₁.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma map_unique (φ' : (relativeGluingData H₁).glued ⟶ (relativeGluingData H₂).glued)
    (hφ' : ∀ U : Y.AffineZariskiSite, (relativeGluingData H₁).cover.f U ≫ φ' =
      Spec.map (β.app (op U)) ≫ (relativeGluingData H₂).cover.f U) :
    φ' = map H₁ H₂ β :=
  (relativeGluingData H₁).cover.hom_ext _ _ fun U ↦ (hφ' U).trans (ι_map H₁ H₂ β U).symm

scoped instance isIso_specMap [IsIso β] : IsIso (specMap H₁ H₂ β) := by
  have : ∀ U, IsIso ((specMap H₁ H₂ β).app U) := fun U ↦ by
    dsimp [specMap]
    exact inferInstanceAs (IsIso (Scheme.Spec.map (β.app (op U)).op))
  exact NatIso.isIso_of_isIso_app _

lemma isIso_map (h : IsIso β) : IsIso (map H₁ H₂ β) := by
  dsimp [map]
  infer_instance

variable (hβ : α₂ ≫ β = α₁)
include hβ

lemma map_toBase : map H₁ H₂ β ≫ (relativeGluingData H₂).toBase = (relativeGluingData H₁).toBase := by
  refine (relativeGluingData H₁).cover.hom_ext _ _ fun U ↦ ?_
  have h1 := ι_map H₁ H₂ β U
  have h2 := ι_toBase H₂ U
  have h3 := ι_toBase H₁ U
  rw [← Category.assoc, h1]
  change Spec.map (β.app (op U)) ≫ (relativeGluingData H₂).cover.f U ≫
    (relativeGluingData H₂).toBase = _
  erw [h2]
  rw [h3, ← Spec.map_comp_assoc, ← NatTrans.comp_app, hβ]

end FormalGAGAFiniteRelSpecMapAux
-- [port] was: p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.FormalGAGAFiniteRelSpecMapAux"
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.FormalGAGAFiniteRelSpecMapAux

end
-- [port] was: p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.FormalGAGAFiniteRelSpecMapAux"
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.FormalGAGAFiniteRelSpecMapAux

open FormalGAGAFiniteRelSpecMapAux in
theorem solution
    {Y : Scheme.{u}} {F₁ F₂ : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α₁ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₁}
    {α₂ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₂}
    (H₁ : α₁.Coequifibered) (H₂ : α₂.Coequifibered) (β : F₂ ⟶ F₁) (hβ : α₂ ≫ β = α₁) :
    ∃ φ : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
        (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
      φ ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).toBase =
        (Scheme.AffineZariskiSite.relativeGluingData H₁).toBase ∧
      (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ =
        Spec.map (β.app (op U)) ≫
          (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) ∧
      (∀ φ' : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
          (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
        (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ' =
          Spec.map (β.app (op U)) ≫
            (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) → φ' = φ) ∧
      (IsIso β → IsIso φ) :=
  ⟨map H₁ H₂ β, map_toBase H₁ H₂ β hβ, ι_map H₁ H₂ β, map_unique H₁ H₂ β, isIso_map H₁ H₂ β⟩
