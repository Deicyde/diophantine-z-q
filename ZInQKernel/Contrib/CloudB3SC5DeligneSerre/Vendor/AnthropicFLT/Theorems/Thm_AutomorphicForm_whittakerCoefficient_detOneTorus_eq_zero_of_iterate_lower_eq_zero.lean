/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero (git blob 01560228ea8865c02bbaed80eb2e4109d093fd02, sha256 dddb584383a45377883e9503bc23826bdcbbe01b7bc395bf6b1540c53da406a1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K), y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (((fun x : AdelicGL2 (𝓞 K) K → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y)) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (y) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 := by
  revert K D w hw y hyc hper hys hD ε hε k₀ M hk₀ n hn hm hΩ hlow g₀ hg₀ C Ngr hgrowth t ht
  exact @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero.solution
