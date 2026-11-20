/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero (git blob 09c9d2fa091608bc97b084049a0c17a95e22bc24, sha256 b770eca57829bfa3db71497c92924376dfe74bb461cdfca1ec7b589fdc4e8bf1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_HeckeEigenfunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

theorem UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen (𝓞 K) K v)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (W W' : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (lam om lam' om' : ℂ)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent x) * g) = ψv x * W g)
    (hN' : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (placeEmbed K v (unipotent x) * g) = ψv x * W' g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hK' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W' (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W' (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W' (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om' * W' g)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) :
    (∀ m : ℕ,
      W ((heckeGen (𝓞 K) K v) ^ m * g) * (starRingEnd ℂ) (W' ((heckeGen (𝓞 K) K v) ^ m * g)) =
        heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m *
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) lam') ((starRingEnd ℂ) om') m *
          (W g * (starRingEnd ℂ) (W' g))) ∧
    (∀ m : ℕ, 0 < m → W ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) := by
  revert K v ψv ϖ hπ hgen I b hI hψ0 hψ1 W W' lam om lam' om' hN hN' hK hK' hT hT' hZ hZ' g hg
  exact @_root_.P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero.solution
