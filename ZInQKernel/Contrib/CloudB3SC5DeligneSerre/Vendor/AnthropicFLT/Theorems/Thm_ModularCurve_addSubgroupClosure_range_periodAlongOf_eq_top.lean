/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top (git blob 18c70c8fdc823062f21186055095d4a2b91e2b57, sha256 aac18269d0578005f939b1ae2f13803ecf7e707aeb5c2bb10492fa188c958721).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) := by
  revert Γ
  exact @_root_.P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.solution
