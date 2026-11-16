/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower
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
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower
    (p : ℕ) [inst_t1 : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] K]
    (c : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b :=
  @_root_.P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower.solution p inst_t1 K inst_t2 c hc hcocycle
