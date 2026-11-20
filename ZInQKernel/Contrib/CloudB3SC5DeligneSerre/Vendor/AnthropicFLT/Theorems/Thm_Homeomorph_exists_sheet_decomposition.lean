/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Homeomorph_exists_sheet_decomposition (git blob ffc02e84d3b120f241cb6518635ebe66c1f1a71f, sha256 4cfc2491e4704efae804fe60fb35b38179c687f61c27cff94d1fd558a7d205a6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Homeomorph_exists_sheet_decomposition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Homeomorph.exists_sheet_decomposition {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {U : Set X}
    {Ω : Set E} (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I) (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source) := by
  revert E X I f U Ω hpre H hH V hV hVU
  exact @_root_.P2MW.S_Homeomorph_exists_sheet_decomposition.solution
