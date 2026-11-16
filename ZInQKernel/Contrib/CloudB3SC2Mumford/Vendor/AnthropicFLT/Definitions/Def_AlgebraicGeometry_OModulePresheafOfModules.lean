/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)

def ofModules : OModulePresheaf π where
  obj U := Γ(M, U)
  addCommGroup _ := inferInstance
  module U := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
  moduleSections _ := inferInstance
  isScalarTower U := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
  res h := Scheme.TwoAffineOpenCover.restrictSections π M h
  res_smul h a x := Scheme.Modules.map_smul M (homOfLE h) a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (le_refl U)).op x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), M.presheaf.map_id]
    rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U''
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (h.trans h')).op x
      = M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

theorem ofModules_obj (U : V.Opens) : (ofModules π M).obj U = Γ(M, U) := rfl

theorem ofModules_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) :
    (ofModules π M).res h (show (ofModules π M).obj U' from x) = M.presheaf.map (homOfLE h).op x :=
  rfl

theorem ofModules_smul (U : V.Opens) (a : Γ(V, U)) (x : Γ(M, U)) :
    (show (ofModules π M).obj U from a • x) = a • (show (ofModules π M).obj U from x) := rfl

theorem ofModules_algebraMap_smul (U : V.Opens) (r : R) (x : (ofModules π M).obj U) :
    r • x = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r • x :=
  rfl

theorem ofModules_twoChartSections (𝒱 : V.TwoAffineOpenCover) :
    (ofModules π M).twoChartSections 𝒱 = 𝒱.sectionsOf π M := rfl

end AlgebraicGeometry.OModulePresheaf

end
