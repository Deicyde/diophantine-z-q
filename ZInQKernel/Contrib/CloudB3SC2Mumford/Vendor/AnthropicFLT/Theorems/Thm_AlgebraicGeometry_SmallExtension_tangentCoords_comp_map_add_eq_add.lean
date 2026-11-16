/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u
theorem AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_add_eq_add
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {A : Type u} [CommRing A] (ψ : A →+* thickening T' (V × V) C) :
    tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V + LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) =
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V))).toRingHom.comp ψ) +
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add.solution
