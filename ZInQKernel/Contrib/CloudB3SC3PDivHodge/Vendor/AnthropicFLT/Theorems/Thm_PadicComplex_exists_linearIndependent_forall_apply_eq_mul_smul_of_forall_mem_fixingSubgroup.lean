/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
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
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
    (p : ℕ) [inst_t1 : Fact p.Prime] {W : Type*} [inst_t2 : AddCommGroup W] [inst_t3 : Module ℂ_[p] W]
    (ρ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W →+ W)
    (hρ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (c : ℂ_[p]) (w : W),
      ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρone : ∀ w : W, ρ 1 w = w)
    (hρmul : ∀ (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℂ_[p]ˣ)
    (hχ : ∀ σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ • ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) = χ τ)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t4 : FiniteDimensional ℚ_[p] K]
    {ι : Type*} [inst_t5 : Finite ι] (f : ι → (W →ₗ[ℂ_[p]] ℂ_[p])) (hf : LinearIndependent ℂ_[p] f)
    (hfK : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      ∀ (i : ι) (x : W), f i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f i x) :
    ∃ f' : ι → (W →ₗ[ℂ_[p]] ℂ_[p]), LinearIndependent ℂ_[p] f' ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (i : ι) (x : W),
        f' i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f' i x :=
  @_root_.P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup.solution p inst_t1 W inst_t2 inst_t3 ρ hρ hρone hρmul χ hχ K inst_t4 ι inst_t5 f hf hfK
