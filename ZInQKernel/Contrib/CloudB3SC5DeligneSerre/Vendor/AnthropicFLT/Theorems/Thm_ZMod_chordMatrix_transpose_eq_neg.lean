/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ZMod_chordMatrix_transpose_eq_neg (git blob c5c40d99b9bd2006129f24f89421edeb57df7205, sha256 44078c57619ac9cdff47ad7f84c152233f99436e6e09927fd70375593f0db9f7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ZMod_chordMatrix_transpose_eq_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ZMod.chordMatrix_transpose_eq_neg {m : ℕ} [NeZero m]
    (a b : Fin m → ZMod (2 * m))
    (hdist : Function.Injective (fun p : Fin m × Bool => bif p.2 then a p.1 else b p.1)) :
    let P : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      (if a j ≠ a i ∧ (a j - a i).val < (b i - a i).val then (1 : ℤ) else 0) -
      (if b j ≠ a i ∧ (b j - a i).val < (b i - a i).val then (1 : ℤ) else 0)
    P.transpose = -P := by
  revert m a b hdist
  exact @_root_.P2MW.S_ZMod_chordMatrix_transpose_eq_neg.solution
