/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow (git blob c606fb59f90f6c7c019bf0c0a3e8691acf1365e2, sha256 6b006fcaca131fb3f31457041c0d9fcc7e96fde22ca20bf51a64da252387c3e5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

theorem solution
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFinTestFactor F (fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => conj (ff b⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ)) := by
  classical
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  obtain ⟨hlc, hK⟩ := hff

  have hone : ∀ k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), k ∈ finiteIntegralGL2 (𝓞 F) F →
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F k)) = 1 := by
    intro k hk
    rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (AdelicDock.finEmbed (𝓞 F) F k)
      (by rw [AdelicDock.glFin_finEmbed]; exact hk)]
    refine Finset.prod_eq_one fun w _ => ?_
    have : NumberField.AdelicVolume.archDetNorm w (AdelicDock.finEmbed (𝓞 F) F k) = 1 := by
      unfold NumberField.AdelicVolume.archDetNorm
      rw [AdelicDock.glArch_finEmbed, map_one, Units.val_one, Matrix.det_one, norm_one]
    rw [this, one_pow]

  have hNlc : IsLocallyConstant fun b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun b => ?_
    have hopen : IsOpen ((fun b' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => b⁻¹ * b') ⁻¹' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :=
      (isOpen_finiteLevelZero (𝓞 F) F (N := ⊤) (by simp)).preimage (continuous_const.mul continuous_id)
    have hmem : b ∈ (fun b' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => b⁻¹ * b') ⁻¹' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      show b⁻¹ * b ∈ finiteIntegralGL2 (𝓞 F) F
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hmem] with b' hb'
    have : b' = b * (b⁻¹ * b') := by group
    conv_lhs => rw [this]
    rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, hone _ hb', mul_one]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.mul ?_ ?_
    · exact (hlc.comp_continuous continuous_inv).comp (fun z : ℂ => conj z)
    · exact hNlc.comp (fun r : ℝ => ((r ^ (-σ) : ℝ) : ℂ))
  · refine HasCompactSupport.intro hK.inv ?_
    intro b hb
    have hb' : b⁻¹ ∉ tsupport ff := fun h => hb (by simpa using Set.inv_mem_inv.mpr h)
    show conj (ff b⁻¹) * _ = 0
    rw [image_eq_zero_of_notMem_tsupport hb', map_zero, zero_mul]
