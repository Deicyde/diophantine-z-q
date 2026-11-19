/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast (git blob 0465c0609561f34ebdb2726186f64aaf14aa4594, sha256 da2070b62e9a1a8b2437820ddb5dfd0e9197e33b2696537046edabbb355377dc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hcomm : ∀ i j, M i * M j = M j * M i)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (K : Type*) [Field K] [CharZero K] :
    ∃ w : Fin d → (Fin n → K), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin K (Set.range fun i => ((M i).transpose).map (Int.cast : ℤ → K))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) K).mulVec (w k))) := by
  revert ι n d M hcomm hfree hmult K
  exact @_root_.P2MW.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast.solution
