/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {X P : Scheme.{u}} [IsIntegral X] (f : X ⟶ P) [IsImmersion f] [QuasiCompact f] :
    ∃ (_ : IsIntegral f.image),
      f.toImage.base (genericPoint X) = genericPoint f.image ∧
      IsIso (f.toImage.stalkMap (genericPoint X)) := by
  have hirr : IrreducibleSpace ↥f.image := by
    rw [irreducibleSpace_def]
    have h1 : IsIrreducible (Set.range ⇑f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rwa [f.toImage.denseRange.closure_range] at h2
  have hcov : ∀ U : P.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have hq : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U) := by
      haveI : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ RingHom.ker (f.app U).hom) :=
        isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)
      exact isReduced_of_injective (Ideal.quotEquivOfEq (f.ker_apply U))
        (Ideal.quotEquivOfEq (f.ker_apply U)).injective
    show IsReduced (Spec (.of (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U)))
    infer_instance
  have hred : IsReduced f.image :=
    @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hcov
  haveI : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced f.image
  exact ⟨this, genericPoint_eq_of_isOpenImmersion f.toImage, inferInstance⟩
