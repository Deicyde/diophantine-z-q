/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_rationalRankTwoNebentypus_family (git blob b5210480fa7db516efe9a78c1b88756f36da18aa, sha256 d4d82845525e4fc54236ec3e8207dfcf83efbefaacdce885c9411f76e115f096).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_rationalRankTwoNebentypus_family

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.rationalRankTwoNebentypus_family :
    ∀ (M p : ℕ) (hM : 0 < M) (hp : p.Prime),
      haveI : Fact p.Prime := ⟨hp⟩
      letI := ModularCurve.heckeModuleOneBar M
      ModularCurve.RationalRankTwoNebentypus M p := @_root_.P2MW.S_ModularCurve_rationalRankTwoNebentypus_family.solution
