/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero (git blob 696cd38e600f01bc6d6294dc55fb6e444af41fcc, sha256 ad9f5d84f8284db1f0db09d5222bb3e480ab568def06e714c17d805d65c87727).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Matrix
open _root_.IsDedekindDomain
open _root_.NumberField
open _root_.NumberField.AdelicLevel
open _root_.AutomorphicForm
open _root_.UnramifiedWhittaker hiding apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
open _root_.AdelicDock

theorem UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∉ S,
      Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) =
        WithZero.exp (-1 : ℤ))
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (lam om : HeightOneSpectrum (𝓞 F) → ℂ)
    (hψ0 : ∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hT : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        om v * W g)
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    (hW : ∃ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W g ≠ 0) :
    ∃ (g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F)) (a₀ : (AdeleRing (𝓞 F) F)ˣ),
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
        ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne a₀ * g₀) ≠ 0 := by
  revert F S W ψ ϖ hπ hϖ I b lam om hψ0 hψ1 hN hT hZ hK hW
  exact @_root_.P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.solution
