/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

theorem Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution
