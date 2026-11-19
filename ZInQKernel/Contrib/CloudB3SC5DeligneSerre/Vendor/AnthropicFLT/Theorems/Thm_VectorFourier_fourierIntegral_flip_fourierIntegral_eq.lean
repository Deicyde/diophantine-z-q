/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq (git blob 32e6df4cdeff15693002e0429905b21f3a4d0a39, sha256 6f0cdc90125d478ed1fc7ba93ca9922ff4f6a4a07464c55ff70125c6ed07b236).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_VectorFourier_fourierIntegral_flip_fourierIntegral_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped FourierTransform SchwartzMap
theorem VectorFourier.fourierIntegral_flip_fourierIntegral_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (f : 𝓢(V, ℂ)) (x : V) :
    VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = ((μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| : ℝ)
        * f (-x) := by
  revert V μ B hB ι b f x
  exact @_root_.P2MW.S_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.solution
