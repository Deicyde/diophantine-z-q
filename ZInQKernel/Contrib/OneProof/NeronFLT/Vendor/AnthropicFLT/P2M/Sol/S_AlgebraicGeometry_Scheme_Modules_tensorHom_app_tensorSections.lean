/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
-- [port] Lean v4.35: backward-compatibility elaboration flags (as in CloudW03NeronSurj's port)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
-- [port] Lean v4.35: instance-search transparency flag (see the adaptation note in Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal)
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

-- [port] Lean v4.35: instance search no longer sees through `(T ⋙ forget₂ CommRingCat RingCat).obj X`
noncomputable def commRingCompForget₂Obj_port_d6eec3 {E : Type*} [CategoryTheory.Category E]
    (T : CategoryTheory.Functor E CommRingCat) (X : E) :
    CommRing ((CategoryTheory.Functor.comp T (CategoryTheory.forget₂ CommRingCat RingCat)).obj X) :=
  inferInstanceAs (CommRing (T.obj X))

attribute [local instance] commRingCompForget₂Obj_port_d6eec3

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "sheafify tensorIsoSheafify tensorSections"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace TensorHomSections

open Opposite TensorProduct



variable {X : Scheme.{u}} {L L' M M' : X.Modules}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

variable (L M)

def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    ((asIso (adj X).counit).app L ⊗ᵢ (asIso (adj X).counit).app M)

variable {L M}

lemma sheafifyTensorIso_hom_naturality (f : L ⟶ L') (g : M ⟶ M') :
    (Modules.sheafify X).map ((ι X).map f ⊗ₘ (ι X).map g) ≫ (sheafifyTensorIso L' M').hom =
      (sheafifyTensorIso L M).hom ≫ (f ⊗ₘ g) := by
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom]
  -- [port] Lean v4.35: the preceding `dsimp only` already performs these rewrites
  try simp only [MonoidalCategory.tensorIso_hom, Iso.app_hom, asIso_hom]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv, ← Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, Category.assoc, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  erw [(adj X).counit.naturality f, (adj X).counit.naturality g]
  rfl

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

theorem tensorHom_app_tensorSections (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (Modules.tensorSections s t) = Modules.tensorSections (φ.app U s) (ψ.app U t) := by
  have h := congr($(sheafifyTensorIso_hom_naturality φ ψ).val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))))

  have h' : (sheafifyTensorIso L' M').hom.val.app (op U)
      (((Modules.sheafify X).map ((ι X).map φ ⊗ₘ (ι X).map ψ)).val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) =
      (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) := h
  rw [tensorSections_eq, tensorSections_eq]
  change (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) = _
  rw [← h']
  erw [sheafify_map_val_app_unit ((ι X).map φ ⊗ₘ (ι X).map ψ) (op U)]
  congr 1
  -- [port] Mathlib v4.35: the monoidal structure on presheaves of modules over CommRingCat moved to `PresheafOfModulesOfCommRing`
  all_goals (erw [PresheafOfModulesOfCommRing.tensorHom_app])
  all_goals exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _

end TensorHomSections

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) :=
  TensorHomSections.tensorHom_app_tensorSections φ ψ s t
