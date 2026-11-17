/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact (git blob d7ee40018bc0b5e698d6cdeee084e3e11b216208, sha256 38689bf954dfa28deb115aff9ddbc140f4d0f5d80981c1c230b8050a0ce6ed01).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

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
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp

  obtain ⟨n, c, ψ, hcd, hψ, hψK, hψf, hψjc, hψhol, hψflat, hsum⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα 1 1 φ hφ hφK hφf hφjc hφhol
  have hψc : ∀ i s, Continuous (ψ i s) := fun i s =>
    (hψjc i).comp (Continuous.prodMk continuous_const continuous_id)
  have hflat := fun i =>
    AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family
      F hα (ψ i) (hψ i) (hψK i) (hψf i) (hψjc i) (hψhol i) (hψflat i)

  have hM : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g
        = ∑ i, c i s * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ i s) g := by
    intro s hs g
    have hint : ∀ i, Integrable (fun x : AdeleRing (𝓞 F) F =>
        ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) := fun i =>
      AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1u h1u s hs (ψ i s) (hψ i s)
        (hψc i s) g
    simp only [weylIntertwiningIntegral]
    have hfun : (fun x : AdeleRing (𝓞 F) F => φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g))
        = fun x => ∑ i, c i s * ψ i s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) :=
      funext (fun x => hsum s _)
    rw [hfun, integral_finsetSum _ (fun i _ => (hint i).const_mul (c i s))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact integral_const_mul _ _

  intro k hkf hka
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ =>
    (((hcd i).continuous.tendsto (1 / 2 : ℂ)).mono_left
      (nhdsWithin_le_nhds (s := {s : ℂ | 1 / 2 < s.re}))).mul (hflat i k hkf hka))
  simp only [mul_zero, Finset.sum_const_zero] at hlim
  refine hlim.congr' ?_
  refine eventually_nhdsWithin_of_forall (fun s hs => ?_)
  beta_reduce
  rw [hM s hs k, hM s hs 1, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring
