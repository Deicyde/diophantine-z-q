/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.sheafify Scheme.Modules.tensorSections)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (tensor sheafify tensorIsoSheafify tensorSections)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

namespace SheafifyMu
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TensorProduct

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

variable (L M : X.Modules)

def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    ((asIso (adj X).counit).app L ⊗ᵢ (asIso (adj X).counit).app M)

variable {L M}

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma map_tensorHom_unit_comp (P Q : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) ≫
      (sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom ≫
        Functor.LaxMonoidal.μ (Modules.sheafify X) P Q = 𝟙 _ := by
  have hP : (Modules.sheafify X).map ((adj X).unit.app P) ≫ (adj X).counit.app ((Modules.sheafify X).obj P) =
      𝟙 _ := (adj X).left_triangle_components P
  have hQ : (Modules.sheafify X).map ((adj X).unit.app Q) ≫ (adj X).counit.app ((Modules.sheafify X).obj Q) =
      𝟙 _ := (adj X).left_triangle_components Q
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom]
  rw [Functor.Monoidal.μIso_inv]
  simp only [← Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app P) ((adj X).unit.app Q)]
  rw [Category.assoc (Functor.OplaxMonoidal.δ (Modules.sheafify X) _ _)]
  erw [MonoidalCategory.tensorHom_comp_tensorHom, hP, hQ]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]
  exact Functor.Monoidal.δ_μ _ _ _

theorem sheafify_μ_app_tensorSections (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (op U)) (y : Q.obj (op U)) :
    (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).app U
      (Modules.tensorSections (L := (Modules.sheafify X).obj P) (M := (Modules.sheafify X).obj Q)
        (((adj X).unit.app P).app (op U) x) (((adj X).unit.app Q).app (op U) y)) =
    ((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y) := by

  have H := congr($(map_tensorHom_unit_comp P Q).val.app (op U)
    (((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y)))

  have h1 := (sheafify_map_val_app_unit ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) (op U)
      (x ⊗ₜ[Γ(X, U)] y)).trans
    (congrArg (((adj X).unit.app ((ι X).obj ((Modules.sheafify X).obj P) ⊗
        (ι X).obj ((Modules.sheafify X).obj Q))).app (op U))
      (ModuleCat.MonoidalCategory.tensorHom_tmul (((adj X).unit.app P).app (op U))
        (((adj X).unit.app Q).app (op U)) x y))
  exact (congrArg (fun z => (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).val.app (op U)
    ((sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom.val.app (op U) z))
      h1).symm.trans H

end SheafifyMu

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry.Scheme.Modules TensorProduct in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (Opposite.op U)) (y : Q.obj (Opposite.op U)) :
    (Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.sheafify X) P Q).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (L := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj P)
        (M := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj Q)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app (Opposite.op U) x)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app (Opposite.op U) y)) =
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (P ⊗ Q)).app (Opposite.op U)
      (x ⊗ₜ[Γ(X, U)] y) :=
  SheafifyMu.sheafify_μ_app_tensorSections P Q x y
