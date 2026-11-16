/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent)
    (W : P.affineOpens) (hW : IsAffineOpen (p ⁻¹ᵁ W.1)) :
    (∀ x y : G.obj (p ⁻¹ᵁ W.1),
        (∀ j : K'.ι, G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x
          = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) y) → x = y) ∧
      ∀ c : (OModulePresheaf.cechPushforward p q K' G).obj W.1,
        ∃ x : G.obj (p ⁻¹ᵁ W.1), ∀ j : K'.ι,
          c.1 j = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.solution
