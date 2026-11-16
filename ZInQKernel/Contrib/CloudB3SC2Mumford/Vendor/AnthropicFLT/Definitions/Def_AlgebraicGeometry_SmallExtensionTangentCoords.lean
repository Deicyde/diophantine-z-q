/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

open TensorProduct IsLocalRing

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

def vPart : thickening T' V C →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)

def tensorToDualHom (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] :
    M ⊗[k] W →ₗ[k] (Module.Dual k W →ₗ[k] M) :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun (m : M) (w : W) => (LinearMap.smulRight (Module.Dual.eval k W w) m : Module.Dual k W →ₗ[k] M))
      (fun m₁ m₂ w => by ext ξ; simp)
      (fun c m w => by ext ξ; simp [smul_smul, mul_comm])
      (fun m w₁ w₂ => by ext ξ; simp [add_smul])
      (fun c m w => by ext ξ; simp [smul_smul]))

@[simp] theorem tensorToDualHom_tmul (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] (m : M) (w : W) (ξ : Module.Dual k W) :
    tensorToDualHom k M W (m ⊗ₜ w) ξ = ξ w • m := by
  simp [tensorToDualHom]

variable (T') in

def tangentCoords {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) :=
  tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a))

theorem tangentCoords_apply {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C φ a ξ = tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a)) ξ := rfl

theorem tangentCoords_add {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a b : A) :
    tangentCoords T' V C φ (a + b) = tangentCoords T' V C φ a + tangentCoords T' V C φ b := by
  unfold tangentCoords
  rw [φ.map_add, LinearMap.map_add, LinearMap.map_add]

end AlgebraicGeometry.SmallExtension

end
