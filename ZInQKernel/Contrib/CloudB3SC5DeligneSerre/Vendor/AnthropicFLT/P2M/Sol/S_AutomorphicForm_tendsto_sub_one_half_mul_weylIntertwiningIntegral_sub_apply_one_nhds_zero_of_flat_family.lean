/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family (git blob 8d3909b983d250c4a44aae10df1290c8d0d18a81, sha256 d2118044b263e50564268fceee41936ac9e5c80f284c09165ebbc2963d09f847).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem weylIntertwiningIntegral_mul_right
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {_inst : MeasurableSpace (AdeleRing R K)} (ν : Measure (AdeleRing R K)) (f : AdelicGL2 R K → ℂ) (g k : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν f (g * k) = weylIntertwiningIntegral R K ν (fun h => f (h * k)) g := by
  simp only [weylIntertwiningIntegral, mul_assoc]

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  classical
  intro α hα

  have main : ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAt F S →
      letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro φ hφ hφK hφf hφjc hφhol hφflat k hk
      exact AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
        F hα φ hφ hφK hφf hφjc hφhol hφflat k hk
    | insert v S' hv IH =>
      intro φ hφ hφK hφf hφjc hφhol hφflat k hk
      obtain ⟨k', kv, hk', hkv, hkv', rfl, hcomm⟩ :=
        AutomorphicForm.exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt F (insert v S') v
          (Finset.mem_insert_self v S') k hk
      rw [Finset.erase_insert hv] at hk'
      have hk'K : k' ∈ adelicMaximalCompact F := maximalCompactAt_le F S' hk'

      obtain ⟨hψ, hψK, hψf, hψjc, hψhol, hψflat⟩ :=
        AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact F hα φ hφ hφK hφf hφjc hφhol hφflat k' hk'K
      have hA := AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton
        F hα (fun s h => φ s (h * k')) hψ hψK hψf hψjc hψhol hψflat v kv hkv hkv'
      have hB := IH φ hφ hφK hφf hφjc hφhol hφflat k' hk'
      have hsum := hA.add hB
      rw [add_zero] at hsum
      refine hsum.congr (fun s => ?_)
      rw [hcomm, weylIntertwiningIntegral_mul_right, ← one_mul k',
        weylIntertwiningIntegral_mul_right (adelicAddHaar (𝓞 F) F) (φ s) 1 k', one_mul]
      ring

  intro φ hφ hφK hφf hφjc hφhol hφflat k hkf hka
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  have hkK : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkf, hka⟩
  obtain ⟨S₀, hS₀⟩ :=
    AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family F hα φ hφ hφK hφf hφjc hφhol hφflat
  obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ :=
    AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq F S₀ k hkK
  have hcut : ∀ s : ℂ, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) (k₁ * k₂)
      = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k₁ := by
    intro s
    simp only [weylIntertwiningIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (k₁ * k₂)) = φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k₁)
    rw [← mul_assoc]
    exact hS₀ s _ k₂ hk₂
  simp_rw [hcut]
  exact main S₀ φ hφ hφK hφf hφjc hφhol hφflat k₁ hk₁
