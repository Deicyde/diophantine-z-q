/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable (git blob 60040a442b0c1e4357e6105f95e9e1519f36f35c, sha256 363c21591851a7cf59bbcce9b04a51480cc16544de76ff1f626f079de3a42f63).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 F) F → ℂ)) (hli : LinearIndependent ℂ x)
    (hR : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) ∈ Submodule.span ℂ (Set.range x))
    (hS : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) ∈
          Submodule.span ℂ (Set.range x))
    (hR' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then 1 else if (p : ℕ) = p' + 1 then -((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) * x p' g) 0)
    (hS' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then Complex.I else if (p : ℕ) = p' + 1 then Complex.I * ((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) *
            x p' g) 0) :
    ∃ E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      E₁ 0 = 1 ∧ E₂ 0 = 1 ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
        (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
        (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₁ s p' p * x p' g) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw
          !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) := by
  revert F w hw n x hli hR hS hR' hS'
  exact @_root_.P2MW.S_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable.solution
