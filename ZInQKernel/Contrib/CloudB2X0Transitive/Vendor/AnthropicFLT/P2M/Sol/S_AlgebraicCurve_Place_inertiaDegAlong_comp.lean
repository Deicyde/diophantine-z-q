/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_inertiaDegAlong_comp
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_comp

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : W.inertiaDegAlong (χ.comp φ) hχφ = W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ := by
  letI iχ : Algebra F' F'' := algebraAlong χ
  haveI := isScalarTower_along χ
  haveI := isIntegral_along χ hχ
  letI iφ : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ

  let w : Place K F' := W.restrict F'
  let v : Place K F := w.restrict F

  letI iχφ : Algebra F F'' := algebraAlong (χ.comp φ)
  haveI := isScalarTower_along (χ.comp φ)
  haveI := isIntegral_along (χ.comp φ) hχφ
  letI : Algebra v.ResidueField W.ResidueField := (Place.restrictResidueMap F W).toAlgebra
  haveI : IsScalarTower v.ResidueField w.ResidueField W.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    show Place.restrictResidueMap F W (IsLocalRing.residue _ a)
      = Place.restrictResidueMap F' W (Place.restrictResidueMap F w (IsLocalRing.residue _ a))
    rw [Place.restrictResidueMap_residue, Place.restrictResidueMap_residue,
      Place.restrictResidueMap_residue]
    exact congrArg _ (Subtype.ext rfl)
  show Module.finrank v.ResidueField W.ResidueField
    = Module.finrank w.ResidueField W.ResidueField * Module.finrank v.ResidueField w.ResidueField
  rw [mul_comm]
  exact (Module.finrank_mul_finrank v.ResidueField w.ResidueField W.ResidueField).symm
