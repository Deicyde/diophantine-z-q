/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq (git blob bf9131c517bce68ac619f9c85f4f9ff5b3873432, sha256 f7bf04b2a41e1ffcd7a7612a5a6e7e8b0e24340a36036975875b1c8796e00a3c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eisenstein4_cube_sub_mk_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.eisenstein4_cube_sub_mk_sq :
    eisenstein4 ^ 3 -
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) ^ 2 =
      1728 * (PowerSeries.X * dedekindEtaUnit) := @_root_.P2MW.S_ModularCurve_eisenstein4_cube_sub_mk_sq.solution
