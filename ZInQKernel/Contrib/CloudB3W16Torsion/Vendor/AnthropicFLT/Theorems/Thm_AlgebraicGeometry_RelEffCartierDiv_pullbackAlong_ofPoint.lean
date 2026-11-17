/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_ofPoint
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.solution
