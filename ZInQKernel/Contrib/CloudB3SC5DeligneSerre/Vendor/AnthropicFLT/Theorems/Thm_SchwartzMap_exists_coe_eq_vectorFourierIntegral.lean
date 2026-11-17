/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral (git blob 96dbfbd61236a53bb18ad86989bdac4c42f04cb9, sha256 39f1e762a986aeecc271fb8ca8ef05e445b0d3b55ef43fa164adc21f88a44107).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_SchwartzMap_exists_coe_eq_vectorFourierIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped FourierTransform SchwartzMap
theorem SchwartzMap.exists_coe_eq_vectorFourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f := by
  revert V μ B hB f
  exact @_root_.P2MW.S_SchwartzMap_exists_coe_eq_vectorFourierIntegral.solution
