/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isStackFor_openCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isStackFor_openCover

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution (Y : Scheme.{u}) (𝒰 : Y.OpenCover) :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).IsStackFor
      (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  set F := ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData 𝒰.f with hF
  have hcov : ∀ y : Y, ∃ i, y ∈ Set.range (𝒰.f i).base := fun y => ⟨𝒰.idx y, 𝒰.covers y⟩
  haveI : F.Faithful :=
    ⟨fun {L₁ L₂} => (Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁ L₂).1⟩
  haveI : F.Full :=
    ⟨fun {L₁ L₂} φ => ⟨_, ((Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁ L₂).2 φ).choose_spec⟩⟩
  haveI : F.EssSurj := Scheme.Modules.toDescentData_essSurj_of_openCover 𝒰.f hcov
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
