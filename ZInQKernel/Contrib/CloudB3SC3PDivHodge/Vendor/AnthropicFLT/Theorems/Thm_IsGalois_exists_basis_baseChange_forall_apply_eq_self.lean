/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_IsGalois_exists_basis_baseChange_forall_apply_eq_self

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct

theorem IsGalois.exists_basis_baseChange_forall_apply_eq_self
    {K L : Type*} [inst_t1 : Field K] [inst_t2 : Field L] [inst_t3 : Algebra K L] [inst_t4 : FiniteDimensional K L] [inst_t5 : IsGalois K L]
    {U : Type*} [inst_t6 : AddCommGroup U] [inst_t7 : Module K U] [inst_t8 : FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  @_root_.P2MW.S_IsGalois_exists_basis_baseChange_forall_apply_eq_self.solution K L inst_t1 inst_t2 inst_t3 inst_t4 inst_t5 U inst_t6 inst_t7 inst_t8 ρ f hf
