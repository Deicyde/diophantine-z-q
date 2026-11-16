/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem Algebra.TensorProduct.nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial (K ⊗[k] R) ∧ ∀ e : K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed.solution
