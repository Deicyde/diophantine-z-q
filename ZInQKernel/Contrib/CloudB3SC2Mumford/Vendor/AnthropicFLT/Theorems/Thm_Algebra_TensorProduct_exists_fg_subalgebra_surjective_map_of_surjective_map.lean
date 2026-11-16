/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map
    {R A D C : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing C] [Algebra R A] [Algebra R D] [Algebra R C]
    (φ : D →ₐ[R] C) (hφ : φ.toRingHom.FiniteType)
    (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ)) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution
