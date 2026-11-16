/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_CompletionBridge
import ZInQKernel.Contrib.CloudB3W11TateTrace.TraceModel
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicComplex.bijOn_towerClosure_smul_sub_mul_of_isTateTrace
    (p : ℕ) [inst_t1 : Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ n, FiniteDimensional ℚ_[p] (Km n))
    (m : ℕ) (d : ℝ) (R : ℂ_[p] → ℂ_[p]) (hR : PadicComplex.IsTateTrace p Km m d R)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (Km m).fixingSubgroup)
    (hσ' : σ ∉ (Km (m + 1)).fixingSubgroup) (hstab : ∀ n, ∀ y ∈ Km n, σ y ∈ Km n)
    (μ : ℚ_[p]) (hμ : μ ≠ 1) (hμd : ‖μ - 1‖ * d < 1) :
    Set.BijOn (fun x : ℂ_[p] => σ • x - algebraMap ℚ_[p] ℂ_[p] μ * x)
      (PadicComplex.towerClosure p Km) (PadicComplex.towerClosure p Km) :=
  @_root_.P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.solution p inst_t1 Km hmono hfin m d R hR σ hσ hσ' hstab μ hμ hμd
