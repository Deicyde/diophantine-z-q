/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd

set_option autoImplicit false

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor repartitions repartitionsOf adeleBdd)
open AlgebraicCurve

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd.AlgebraicCurve WithZero in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl
