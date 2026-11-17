/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_hasCanonicalLocalResidueK (git blob 94fce5ba5ea1e12db18de4b4ad35facb87f626d8, sha256 3575bdeb899ba153cde0b75ea43668026b088ebaee9f3e1e28491746f62ab6b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_hasCanonicalLocalResidueK

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.hasCanonicalLocalResidueK
    (K F : Type*) [Field K] [Field F] [Algebra K F] :
    AlgebraicCurve.HasCanonicalLocalResidueK K F := by
  revert K F
  exact @_root_.P2MW.S_AlgebraicCurve_hasCanonicalLocalResidueK.solution
