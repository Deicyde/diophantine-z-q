/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice (git blob 7300db9be38caf6875c2832a955e65faecb2c30e, sha256 4bbce20a9ecb02b5ac591e71df42b8fb3cf391a0c65881702f2319f094e39129).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical nonZeroDivisors

theorem solution
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  have hB : (Algebra.traceForm ℝ (mixedSpace K)).flip.Nondegenerate :=
    (NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate K).flip
  have hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero I

  have hspan : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
    ext x
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, mem_span_basisOfFractionalIdeal]
    rfl

  have hdual : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual) := by
    rw [FractionalIdeal.coe_dual ℤ ℚ hI]
    exact Submodule.traceDual_span_of_basis ℤ _ (basisOfFractionalIdeal K I) hspan

  have hdb : ⇑((Algebra.traceForm ℝ (mixedSpace K)).flip.dualBasis hB
        (fractionalIdealLatticeBasis K I))
      = fun i => mixedEmbedding K ((basisOfFractionalIdeal K I).traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [LinearMap.BilinForm.flip_apply, fractionalIdealLatticeBasis_apply, Algebra.traceForm_apply,
      ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding, Basis.trace_mul_traceDual]
    split_ifs <;> simp
  have himage : (⇑(mixedEmbedding K) '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K))
      = ((Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual)).map
          (mixedEmbedding K).toIntAlgHom.toLinearMap : Set (mixedSpace K)) := by
    rw [Submodule.map_coe, ← hdual]
    rfl
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, hdb, himage,
    Submodule.map_span, ← Set.range_comp]
  rfl
