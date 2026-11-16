/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Fintype ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type v} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    {N₂ : ι → ι → Type v} [∀ i j, AddCommGroup (N₂ i j)] [∀ i j, Module R (N₂ i j)]
    (l : ∀ i j, N i →ₗ[R] N₂ i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g j)) (l i j)]
    (l' : ∀ i j, N j →ₗ[R] N₂ i j) (hll : ∀ i j, l i j ∘ₗ f i = l' i j ∘ₗ f j)
    (x : ∀ i, N i) (hx : ∀ i j, l i j (x i) = l' i j (x j)) :
    ∃ m : M, ∀ i, f i m = x i := by p2m_exact_reverting @_root_.P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution
