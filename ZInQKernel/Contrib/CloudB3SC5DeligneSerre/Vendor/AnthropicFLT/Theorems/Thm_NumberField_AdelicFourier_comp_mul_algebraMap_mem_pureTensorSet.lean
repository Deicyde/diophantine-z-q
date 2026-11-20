/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet (git blob 6f16bc3d686b3d40bfa53e14ad3a6880212be1e9, sha256 925c05c7ef744bed89506e236c8bf534829a6951621e90e92f7d791c01affd64).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F] {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by
  revert F a ha f hf
  exact @_root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.solution
