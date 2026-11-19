/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat (git blob 51d27357ea71a6a3de33943a28eba21630bc5942, sha256 4211eba5cd8ad40da55f051e3f493852b70950e469118381b9e4c574930a51af).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat

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

theorem AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (σ : ℝ)
    (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)
    (hecl : ∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ)
    (hefl : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ))
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x)
    (hhf : ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) :
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
          e p.1 * e p.2 * h ((ι p.1)⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι p.2)⁻¹)
          ∂(μ.prod μ)) =
      ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) =
        conj (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹) ∂(μ.prod μ)) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
  revert F μ ι hι σ e hecl hefl h hhc hhf
  exact @_root_.P2MW.S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat.solution
