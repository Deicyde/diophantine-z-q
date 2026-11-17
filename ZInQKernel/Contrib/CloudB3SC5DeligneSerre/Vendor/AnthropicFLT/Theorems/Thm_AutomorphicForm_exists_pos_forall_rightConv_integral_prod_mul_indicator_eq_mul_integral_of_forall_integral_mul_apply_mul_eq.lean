/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq (git blob c58e02f0764b387d397202fd9ea4cbb947f40def, sha256 f95a03cffcd452f08d3109e10d1c56c1e12e87c7071a39cca36ca39c026bc532).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq

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

theorem AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F)) (hιc : Continuous ι)
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μa.IsHaarMeasure] [μa.IsMulRightInvariant]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ), Continuous e →
      ∀ (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ), Continuous h → HasCompactSupport h →
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
          h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y) →
      ∀ (x : AdelicGL2 (𝓞 F) F → ℂ), Continuous x → (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g) →
        (∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * x (z * adelicArchGLIncl F (ι κ)) ∂μ = x z) →
      ∀ g : AdelicGL2 (𝓞 F) F,
        rightConv F x
            (fun y => (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
                e p.1 * e p.2 * h ((ι p.1)⁻¹ * glArch (𝓞 F) F y * (ι p.2)⁻¹) ∂(μ.prod μ)) *
              Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y)) g
          = C * ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa := by
  revert F μ ι hιc hι μa U hUf hUo hUc
  exact @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq.solution
