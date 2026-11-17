/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isCusp_iff_ord_neg (git blob 6d3da792120981a1e98dbc558e05892fdc8de0f2, sha256 51f725f24895183b6e36bba86b5972d933ca2aab4b2ff20c1775b6475af1503c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QAdicPlace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isCusp_iff_ord_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_iff_ord_neg {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E] (j : E) (v : Place K E) : IsCusp j v ↔ v.ord j < 0 := by
  revert K E j v
  exact @_root_.P2MW.S_ModularCurve_isCusp_iff_ord_neg.solution
