/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_exists_fundamentalCycles_of_spanningTree (git blob b70b2536af4906a970081e10eceec2bccbc8f0a9, sha256 c62e0011f663cc06e4bf830dddd4f176a2bb2c6fd62991b8c36846d9f5bb7df7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_exists_fundamentalCycles_of_spanningTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem exists_fundamentalCycles_of_spanningTree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V) (T : Finset E)
    (hTpath : ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ Z : E → E → ℤ,
      (∀ j, ∀ w, (∑ e with hd e = w, Z j e) = (∑ e with tl e = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {A : Type*} [inst : AddCommGroup A] (f : E → A),
        (∀ w, (∑ e with hd e = w, f e) = (∑ e with tl e = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  revert V E hd tl T hTpath
  exact @_root_.P2MW.S_exists_fundamentalCycles_of_spanningTree.solution
