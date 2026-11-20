/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule (git blob 3fa53a94e4c745cf089cbd460d42bef347e983f3, sha256 455b274bd14654e7541459b670f70035b9f64dc8ab54b1f0cf76e7a38b7e3fbc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped FourierTransform SchwartzMap
theorem ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    Summable fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
      VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by
  revert V μ B hB L f t
  exact @_root_.P2MW.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule.solution
