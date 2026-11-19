/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul (git blob ac255f6ccd3733e1a5b858f5f95e8ab56c72aaaa, sha256 169867f84404f6ac1e26333d7672e330be526d3490798e2ad5881e8ad9b02cc2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_self

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul.AutomorphicForm
open _root_.AutomorphicForm.WindowedSiegel
open _root_.AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
export _root_.AutomorphicForm (productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup IsSmoothCuspAutomorphicFnAt rightConv archEntries IsFactorizableTestFn finiteDimensional_of_forall_mem_rightConv_eq_self)
namespace C8EigenSlice
open _root_.AutomorphicForm

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem isFactorizableTestFn_const_smul {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (a : ℂ) :
    IsFactorizableTestFn F (fun x => a * f x) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩, hff, hfac⟩ := hf
  refine ⟨fun y => a * fa y, ff, ⟨⟨fun e => a * Φ e, contDiff_const.mul hΦ, fun g => by
      show a * fa g = a * Φ (archEntries F g); rw [hfaΦ]⟩, ?_⟩, hff,
    fun g => by show a * f g = a * fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g); rw [hfac, mul_assoc]⟩
  exact hsupp.mul_left

theorem rightConv_const_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (a : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ (fun x => a * f x) g = a * rightConv F φ f g := by
  simp only [rightConv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end AutomorphicForm.C8EigenSlice

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (lam : ℂ) (hlam : lam ≠ 0)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hE : ∀ φ ∈ E, IsSmoothCuspAutomorphicFnAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ φ ∧
      Continuous φ ∧ rightConv F φ f = lam • φ) :
    FiniteDimensional ℂ ↥E := by
  refine AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self F c u d₁ d₂ T hc hd₁ hd hcov ξ
    (fun x => lam⁻¹ * f x) (AutomorphicForm.C8EigenSlice.isFactorizableTestFn_const_smul hf lam⁻¹) E
    fun φ hφ => ?_
  obtain ⟨h1, h2, h3⟩ := hE φ hφ
  refine ⟨h1, h2, ?_⟩
  funext g
  rw [AutomorphicForm.C8EigenSlice.rightConv_const_mul_right, h3, Pi.smul_apply, smul_eq_mul,
    inv_mul_cancel_left₀ hlam]
