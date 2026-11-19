/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat (git blob ca6e157e4716362afa162d8f47a6c57357b8df43, sha256 34235a231f0032c83f9e212ac731ca4b8427fb77499516ca679114d79e19dcfc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (V : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hV : V ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      IsArchTestFactor F h ∧
      (∀ x, (((h x).re : ℝ) : ℂ) = h x ∧ 0 ≤ (h x).re) ∧
      0 < (h 1).re ∧
      tsupport h ⊆ V ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
  revert F σ V hV
  exact @_root_.P2MW.S_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat.solution
