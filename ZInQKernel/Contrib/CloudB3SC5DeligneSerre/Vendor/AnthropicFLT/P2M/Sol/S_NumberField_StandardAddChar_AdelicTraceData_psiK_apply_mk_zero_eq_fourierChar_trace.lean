/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace (git blob 5c9aeb6129018fdf5b3916470f3c1fd061f8108b, sha256 5388593a2ca522c5d5b63f04c5236140d40a77586d5708843e74f8c862fa2752).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_StandardGlobalAddChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Mathlib.Analysis.Fourier.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F] (T : AdelicTraceData F) (x : InfiniteAdeleRing F) :
    T.psiK (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by

  set f : InfiniteAdeleRing F → ℂ := fun x => T.psiK (x, 0) with hf
  set g : InfiniteAdeleRing F → ℂ := fun x => (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) with hg
  suffices hfg : f = g from congrFun hfg x
  have hfc : Continuous f :=
    T.continuous_psiK.comp (continuous_id.prodMk continuous_const :
      Continuous (fun x : InfiniteAdeleRing F => ((x, 0) : AdeleRing (𝓞 F) F)))
  have htr : Continuous (fun x : InfiniteAdeleRing F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) :=
    (LinearMap.continuous_of_finiteDimensional _).comp
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F)
  have hgc : Continuous g := by
    have hg' : g = fun x => Complex.exp (((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) * Complex.I) :=
      funext fun x => Real.fourierChar_apply _
    rw [hg']
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul htr)).mul
      continuous_const)
  refine Continuous.ext_on (InfiniteAdeleRing.denseRange_algebraMap F) hfc hgc ?_
  rintro _ ⟨q, rfl⟩
  simp only [hf, hg]

  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  rw [show ((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F).1
      = algebraMap F (InfiniteAdeleRing F) q from rfl,
    show ((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F).2
      = 0 from rfl, map_zero, AddChar.map_zero_eq_one, mul_one, T.traceInf_algebraMap, psiArch_algebraMap]

  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, NumberField.mixedEmbedding.trace_mixedEmbedding,
    Real.fourierChar_apply]
  push_cast
  ring_nf
