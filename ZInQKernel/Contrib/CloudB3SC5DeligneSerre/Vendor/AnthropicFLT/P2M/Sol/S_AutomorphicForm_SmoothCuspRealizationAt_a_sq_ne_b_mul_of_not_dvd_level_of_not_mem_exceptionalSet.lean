/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet (git blob 67f9d24f5e73fe5fa3891ddadd5ab83c363c6a52, sha256 c26f69ae8e33bb87486c608867f11510d48f5853efb1a23ffd6ee3f83bed6297).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NarrowRayClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10G

theorem solution_aux
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) := by
  intro v hvl hve

  obtain ⟨hICC, -, hcontImp⟩ := AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine K
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)
    Θ.toRawCentral R
  have hχc := hcontImp hR
  obtain ⟨s, hs⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K _ hICC hχc
  have hs' : ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      ‖((R.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K x ^ s := by
    intro x
    first | exact hs x | simpa using hs x

  obtain ⟨S, hSs, hSfd⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  obtain ⟨-, hne, hcross⟩ := AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain K c u d₁ d₂ T hd hcov Θ Θ R R hR s hs' 1 2 one_pos one_lt_two S hSs hSfd
  obtain ⟨-, P, hPcov, -, hPagree⟩ := hcross rfl

  have hRmem : R.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) :=
    Submodule.subset_span ⟨1, funext fun z => by simp⟩
  have hPcov' : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x y : AdelicGL2 (𝓞 K) K → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 K) K => fun z => R.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y :=
    fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
  have hPself : P R.toFun R.toFun ≠ 0 := by
    rw [hPagree R.toFun R.toFun (Submodule.mem_sup_left hRmem) hRmem]
    exact hne

  have hw := AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ R P s hPcov' hPself

  set t : ℝ := (1 - s) / 2 with ht
  obtain ⟨R', hR', hexc, -⟩ := AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul K c u d₁ d₂ T hd₁ Θ R hR t
  have hb' : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level → v ∉ R'.exceptionalSet →
      ‖(Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b v‖ = 1 := by
    intro v hvl' hve'
    rw [hexc] at hve'
    have hvl0 : ¬ v.asIdeal ∣ Θ.level := hvl'
    have hbv : ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) := (hw v hve' hvl0).2
    have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity
    simp only [HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, hbv]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hN.le _), ← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      show ((Ideal.absNorm v.asIdeal : ℝ)) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) from rfl,
      ← Real.rpow_add hN, ht]
    norm_num

  have hve' : v ∉ R'.exceptionalSet := by rw [hexc]; exact hve
  have hvl' : ¬ v.asIdeal ∣ (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).level := hvl
  have hgen := (LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet K c u d₁ d₂ T hc hd₁ hd hcov
    (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))) R' hR' hb' v hvl' hve').1

  intro h
  apply hgen
  simp only [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b]
  rw [mul_pow, h]
  ring

end RS10G

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) :=
  RS10G.solution_aux K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR
