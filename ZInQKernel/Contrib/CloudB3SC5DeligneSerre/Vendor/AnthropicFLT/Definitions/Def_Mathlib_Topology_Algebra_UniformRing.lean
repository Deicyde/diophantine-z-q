/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_Topology_Algebra_UniformRing (git blob 114e2d3931b1e113afc593e4d49bd424c5c299a1, sha256 9d04e834c941cfb89114e09cb2c105dcb728f0b37f21366c5ad77bcf49666817).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_Algebra_Algebra_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

variable {f}

noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    SemialgHom f (Completion α) (Completion β) where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr
    exact extensionHom_coe _ _ m

theorem mapSemialgHom_apply {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f)
    (x : UniformSpace.Completion α) :
    mapSemialgHom f hf x = UniformSpace.Completion.map f x := rfl

theorem mapSemialgHom_coe {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] {f : α →+* β} (hf : UniformContinuous f)
    (a : α) :
    mapSemialgHom f hf.continuous a = f a := by
  rw [mapSemialgHom_apply, map_coe hf]

end UniformSpace.Completion
