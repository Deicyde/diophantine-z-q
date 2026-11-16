/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicComplex_exists_isTateTrace_cyclotomicTower
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11TateTrace.TraceModel
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_CompletionBridge
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3W11TateTrace.CyclotomicTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicComplex.exists_isTateTrace_cyclotomicTower (p : ℕ) [inst_t1 : Fact p.Prime] :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
      PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R :=
  -- [port] proved by the W11 port of the upstream solution (not duplicated here)
  @ZInQ.Contrib.CloudB3W11TateTrace.CyclotomicTrace.solution p inst_t1
