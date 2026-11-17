/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le (git blob 9a2d5dd902a0f2740b8431980285d5fce2ab4265, sha256 e32457b7d4233e27dc29ff5f7e437289310b45dc23981741f1636e01da864faa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K := by
  revert F c u T' hc
  exact @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.solution
