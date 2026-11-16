/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace CSAux
open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

theorem vPart_map (h : (V × V) →ₗ[ResidueField T'] V) (e : thickening T' (V × V) C) :
    vPart T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map h)) e) =
      TensorProduct.map LinearMap.id (h ∘ₗ TrivSqZeroExt.sndHom (ResidueField T') (V × V)) e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c x =>
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    show (TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)) (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    congr 1
    show (TrivSqZeroExt.map h x).snd = h x.snd
    exact TrivSqZeroExt.snd_map h x
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem vPart_map' (h : (V × V) →ₗ[ResidueField T'] V) (e : thickening T' (V × V) C) :
    vPart T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map h)).toRingHom e) =
      TensorProduct.map LinearMap.id (h ∘ₗ TrivSqZeroExt.sndHom (ResidueField T') (V × V)) e :=
  vPart_map V C h e

end CSAux

open AlgebraicGeometry.SmallExtension

theorem solution
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
        (TrivSqZeroExt.map (LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) := by
  funext a
  show tensorToDualHom _ _ _ (vPart T' V C _) = tensorToDualHom _ _ _ (vPart T' V C _) + tensorToDualHom _ _ _ (vPart T' V C _)
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
  rw [CSAux.vPart_map', CSAux.vPart_map', CSAux.vPart_map', LinearMap.add_comp, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
