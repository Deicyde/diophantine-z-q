/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_ModularCurve_CanonicalDivisorUniformizer. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
