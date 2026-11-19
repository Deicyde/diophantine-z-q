/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const (git blob d5e7501e553e0f97cb5cd705b93412db808dcbc1, sha256 e4ed8bfaa271a54b67139b6f73d1c0d964716322c2cd819f6292ce03c6e15666).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace RS11CS

variable (K : Type) [Field K] [NumberField K]

private theorem ideleNorm_eq_one_of_mem_principalIdeles {γ : (AdeleRing (𝓞 K) K)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) : ideleNorm K γ = 1 := by
  obtain ⟨a, rfl⟩ := hγ
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  convert @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) a using 2 <;> try first | with_reducible_and_instances rfl | rfl

end RS11CS

open RS11CS in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂}) = C := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  haveI : Countable Kˣ := Units.val_injective.countable
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := by
    have h : Countable (Set.range (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))) :=
      (Set.countable_range _).to_subtype
    exact h
  set μ := NumberField.Idele.idelicHaar K with hμ
  have hcont : Continuous (ideleNorm K) := NumberField.TateGlobal.continuous_ideleNorm K

  set S : ℝ → Set (AdeleRing (𝓞 K) K)ˣ := fun r => {z | ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂} with hS
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    (isClosed_Icc.preimage ((hcont.pow 2).mul continuous_const)).measurableSet

  have he₂ : 0 < e₂ := he₁.trans he
  have hS1 : S 1 = {z | ideleNorm K z ∈ Set.Icc (Real.sqrt e₁) (Real.sqrt e₂)} := by
    ext z
    simp only [hS, Set.mem_setOf_eq, mul_one, Set.mem_Icc]
    have hz : 0 ≤ ideleNorm K z := (ideleNorm_pos z).le
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := Real.sqrt_le_sqrt h1; rwa [Real.sqrt_sq hz] at this
      · have := Real.sqrt_le_sqrt h2; rwa [Real.sqrt_sq hz] at this
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith [Real.sq_sqrt he₁.le, Real.sqrt_nonneg e₁]
      · nlinarith [Real.sq_sqrt he₂.le, Real.sqrt_nonneg e₂]
  obtain ⟨hpos, hfin⟩ := NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top K D hD hDF
    (Real.sqrt e₁) (Real.sqrt e₂) (Real.sqrt_pos.mpr he₁) (Real.sqrt_lt_sqrt he₁.le he)
  rw [← hS1] at hpos hfin
  refine ⟨μ (D ∩ S 1), hpos.ne', hfin.ne, fun r hr => ?_⟩

  obtain ⟨s, -, hs⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt r) (Real.sqrt_pos.mpr hr)
  set f : (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 K) K)ˣ := fun z => s * z with hf
  have hSr : S r = f ⁻¹' (S 1) := by
    ext z
    simp only [hS, hf, Set.mem_preimage, Set.mem_setOf_eq, ideleNorm_mul, hs, mul_one, mul_pow, Real.sq_sqrt hr.le]
    rw [mul_comm]

  have hpre : D ∩ f ⁻¹' (S 1) = f ⁻¹' (f '' D ∩ S 1) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hz, h1⟩; exact ⟨⟨z, hz, rfl⟩, h1⟩
    · rintro ⟨⟨w, hw, hwz⟩, h1⟩
      have : w = z := mul_left_cancel (hwz : s * w = s * z)
      exact ⟨this ▸ hw, h1⟩
  have hsD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) (f '' D) μ := by
    have h := hDF.image_of_equiv (ν := μ) (Equiv.mulLeft s)
      (by exact (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving) (Equiv.refl _) (fun γ z => by
        show s * ((γ : (AdeleRing (𝓞 K) K)ˣ) * z) = (γ : (AdeleRing (𝓞 K) K)ˣ) * (s * z)
        rw [mul_left_comm])
    exact h

  have hinv : ∀ γ : M4aHerbrand.principalIdeles (𝓞 K) K, (fun z => γ • z) ⁻¹' (S 1) = S 1 := by
    intro γ
    ext z
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul,
      RS11CS.ideleNorm_eq_one_of_mem_principalIdeles K γ.2, one_mul]
  show μ (D ∩ S r) = μ (D ∩ S 1)
  rw [hSr, hpre, measure_preimage_mul, Set.inter_comm, hsD.measure_set_eq hDF (hSm 1) hinv, Set.inter_comm]
