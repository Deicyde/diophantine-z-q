/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections. Apache-2.0.
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.tensorSections)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (sheafify tensorSections)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

namespace UnitorSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((ι X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

def unitTensorIso : (Modules.sheafify X).obj (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N) ≅ 𝟙_ X.Modules ⊗ N :=
  (Functor.Monoidal.μIso (Modules.sheafify X) (𝟙_ X.PresheafOfModules) ((ι X).obj N)).symm ≪≫
    ((Functor.Monoidal.εIso (Modules.sheafify X)).symm ⊗ᵢ (asIso (adj X).counit).app N)

lemma unitTensorIso_hom_comp_leftUnitor_hom :
    (unitTensorIso N).hom ≫ (λ_ N).hom =
      (Modules.sheafify X).map (λ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N := by
  dsimp only [unitTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_inv]
  rw [MonoidalCategory.tensorIso_hom, Iso.app_hom, asIso_hom, Iso.symm_hom]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, Functor.Monoidal.map_leftUnitor,
    MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← MonoidalCategory.leftUnitor_naturality ((adj X).counit.app N)]
  all_goals rfl

theorem leftUnitor_hom_app_tensorSections {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U (Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by
  have h := congr($(unitTensorIso_hom_comp_leftUnitor_hom N).val.app (op U)
    (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
      ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U)))))
  have h' : (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (λ_ ((ι X).obj N)).hom).val.app (op U)
        (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
          ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) := h
  change (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) = g • n
  rw [h']
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))

  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (λ_ ((ι X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply _ _))

end UnitorSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n :=
  UnitorSections.leftUnitor_hom_app_tensorSections N g n
