/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
    {U W : Scheme.{u}} (v : U ⟶ W) (u : U)
    [IsDomain (U.presheaf.stalk u)] [IsDomain (W.presheaf.stalk (v.base u))]
    (U' : U.Opens) [IsOpenImmersion (U'.ι ≫ v)] (hU' : ∃ x : U, x ∈ U' ∧ x ⤳ u) :
    letI : Algebra (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) :=
      ((algebraMap (U.presheaf.stalk u) (FractionRing (U.presheaf.stalk u))).comp (v.stalkMap u).hom).toAlgebra
    IsFractionRing (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict.solution
