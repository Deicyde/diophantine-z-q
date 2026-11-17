/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le (git blob 8d2f7fb647be704813d070cb0d2695c98a39e932, sha256 ac3df3f65facae8b8406031ce7cceb17ddab38d86e2621e3d0d641b6b2179909).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : Y ≤ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by
  classical
  haveI : FiniteDimensional ℂ ↥Y := hY

  obtain ⟨f, hf, hlim⟩ :=
    AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional F N hN tys σ Y hY hYc
      (fun y hy g k hk => hYU hy g k hk) hYt

  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ n, ∀ y : AdelicGL2 (𝓞 F) F → ℂ, Continuous y → ∀ g : AdelicGL2 (𝓞 F) F,
      Integrable (fun x => y (g * x) * f n x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro n y hy g
    obtain ⟨hfc, hfK⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F (f n) (hf n).1
    refine Continuous.integrable_of_hasCompactSupport ((hy.comp (continuous_const_mul g)).mul hfc) ?_
    exact hfK.mul_left
  have hadd : ∀ n (y₁ y₂ : AdelicGL2 (𝓞 F) F → ℂ), Continuous y₁ → Continuous y₂ →
      rightConv F (y₁ + y₂) (f n) = rightConv F y₁ (f n) + rightConv F y₂ (f n) := by
    intro n y₁ y₂ h₁ h₂
    funext g
    simp only [rightConv, Pi.add_apply, add_mul]
    exact integral_add (hint n y₁ h₁ g) (hint n y₂ h₂ g)
  have hsmul : ∀ n (c : ℂ) (y : AdelicGL2 (𝓞 F) F → ℂ),
      rightConv F (c • y) (f n) = c • rightConv F y (f n) := by
    intro n c y
    funext g
    simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  let T : ℕ → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) := fun n =>
    { toFun := fun y => rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) (f n)
      map_add' := fun y₁ y₂ => by
        simpa only [Submodule.coe_add] using hadd n _ _ (hYc _ y₁.2) (hYc _ y₂.2)
      map_smul' := fun c y => by
        simpa only [Submodule.coe_smul, RingHom.id_apply] using hsmul n c _ }
  have hT : ∀ (y : ↥Y) (x : AdelicGL2 (𝓞 F) F),
      Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : AdelicGL2 (𝓞 F) F → ℂ) x)) :=
    fun y x => hlim y y.2 x
  obtain ⟨n, hn⟩ := LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional Y T hT
  refine ⟨f n, (hf n).1, (hf n).2.1, (hf n).2.2, fun y hy h0 => ?_⟩
  have := hn ⟨y, hy⟩ h0
  exact congrArg Subtype.val this
