/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
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
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
    (p : ℕ) [inst_t1 : Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hF : ∀ (L : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F L] (x : F),
      ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F L y = x)
    (c : F.fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : F.fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : F.fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b :=
  @_root_.P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq.solution p inst_t1 F hF c hc hcocycle
