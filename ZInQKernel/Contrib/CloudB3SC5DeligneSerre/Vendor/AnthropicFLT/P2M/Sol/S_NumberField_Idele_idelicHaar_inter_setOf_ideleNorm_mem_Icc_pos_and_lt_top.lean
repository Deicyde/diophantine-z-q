/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top (git blob 03502af6f88fd7521daf9c7d964d6ebc52519067, sha256 1786c779f5a65fc228c6504a48c2de081d37d47266f12cc08900905a2aa1652b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace Vol17

open scoped Pointwise

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

private scoped instance countableK : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

private scoped instance countableKunits : Countable Kˣ := Function.Injective.countable fun _ _ h => Units.ext h

private scoped instance countablePrincipalIdeles : Countable ↥(M4aHerbrand.principalIdeles (𝓞 K) K) := by
  unfold M4aHerbrand.principalIdeles
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

private theorem ideleNorm_eq_one_of_mem {γ : (AdeleRing (𝓞 K) K)ˣ} (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) :
    ideleNorm K γ = 1 := by
  obtain ⟨u, rfl⟩ := hγ
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  convert @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) u using 2 <;> try first | with_reducible_and_instances rfl | rfl

private theorem smul_slab_eq (S : Set ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    γ • {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ S} = {z | ideleNorm K z ∈ S} := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have h1 : ideleNorm K ((γ : (AdeleRing (𝓞 K) K)ˣ)⁻¹) = 1 := by
    rw [← Subgroup.coe_inv]; exact ideleNorm_eq_one_of_mem K (γ⁻¹).2
  simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul, Subgroup.coe_inv, h1, one_mul]

private theorem preimage_slab_eq (S : Set ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    (fun z : (AdeleRing (𝓞 K) K)ˣ => γ • z) ⁻¹' {z | ideleNorm K z ∈ S} = {z | ideleNorm K z ∈ S} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul, ideleNorm_eq_one_of_mem K γ.2,
    one_mul]

private theorem measurableSet_slab {S : Set ℝ} (hS : MeasurableSet S) : MeasurableSet {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ S} :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable hS

private theorem finite_on_tate (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ D₀ : Set (AdeleRing (𝓞 K) K)ˣ, MeasurableSet D₀ ∧
      IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D₀ (NumberField.Idele.idelicHaar K) ∧
      (NumberField.Idele.idelicHaar K) (D₀ ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ := by
  obtain ⟨D₀, hD₀m, hD₀F, hint⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
      (NumberField.Idele.idelicHaar K)
  obtain ⟨k, hk⟩ := hint 0
  refine ⟨D₀, hD₀m, hD₀F, ?_⟩
  set A : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Icc a b} with hA
  set c : ℝ := min a b⁻¹ with hc
  have hcpos : 0 < c := lt_min ha (inv_pos.mpr (ha.trans hab))
  have hb : 0 < b := ha.trans hab

  have hlow : ∀ z ∈ D₀ ∩ A, ENNReal.ofReal (c ^ k) ≤
      ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ := by
    rintro z ⟨-, hz1, hz2⟩
    rw [Real.rpow_zero, mul_one, Real.enorm_eq_ofReal (pow_nonneg (le_min (ideleNorm_pos z).le (inv_nonneg.mpr (ideleNorm_pos z).le)) _)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hcpos.le (le_min ?_ ?_) _)
    · exact (min_le_left _ _).trans hz1
    · exact (min_le_right _ _).trans ((inv_le_inv₀ hb (ideleNorm_pos z)).mpr hz2)
  have hmeas : MeasurableSet (D₀ ∩ A) := hD₀m.inter (measurableSet_slab K measurableSet_Icc)
  have h1 : ENNReal.ofReal (c ^ k) * (NumberField.Idele.idelicHaar K) (D₀ ∩ A) ≤
      ∫⁻ z in D₀, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ ∂(NumberField.Idele.idelicHaar K) := by
    calc ENNReal.ofReal (c ^ k) * (NumberField.Idele.idelicHaar K) (D₀ ∩ A)
        = ∫⁻ z in D₀ ∩ A, ENNReal.ofReal (c ^ k) ∂(NumberField.Idele.idelicHaar K) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in D₀ ∩ A, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ ∂(NumberField.Idele.idelicHaar K) :=
          setLIntegral_mono' hmeas hlow
      _ ≤ ∫⁻ z in D₀, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ ∂(NumberField.Idele.idelicHaar K) :=
          lintegral_mono_set Set.inter_subset_left
  have h2 := hk.2
  rw [HasFiniteIntegral] at h2
  have hck : ENNReal.ofReal (c ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hcpos k)).ne'
  exact (ENNReal.le_div_iff_mul_le (Or.inl hck) (Or.inl ENNReal.ofReal_ne_top)).mpr (by rwa [mul_comm]) |>.trans_lt
    (ENNReal.div_lt_top h2.ne hck)

private theorem main (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) ∧
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ := by
  set μ := NumberField.Idele.idelicHaar K with hμ
  set A : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Icc a b} with hA
  have hAm : MeasurableSet A := measurableSet_slab K measurableSet_Icc
  have hAinv : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K), (fun z => γ • z) ⁻¹' A = A := fun γ => preimage_slab_eq K _ γ
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨z₀, -, hz₀⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K ((a + b) / 2) (by linarith)
    set U : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Ioo a b} with hU
    have hUopen : IsOpen U := isOpen_Ioo.preimage (NumberField.TateGlobal.continuous_ideleNorm K)
    have hUne : U.Nonempty := ⟨z₀, by rw [hU, Set.mem_setOf_eq, hz₀]; constructor <;> linarith⟩
    have hUpos : 0 < μ U := hUopen.measure_pos μ hUne
    have hUA : U ⊆ A := fun z hz => Set.Ioo_subset_Icc_self hz
    have hApos : 0 < μ A := hUpos.trans_le (measure_mono hUA)
    rw [pos_iff_ne_zero]
    intro h0
    have hsum := hDF.measure_eq_tsum A
    have hterm : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K), μ (γ • A ∩ D) = 0 := by
      intro γ
      rw [smul_slab_eq K _ γ, Set.inter_comm]
      exact h0
    simp only [hterm, tsum_zero] at hsum
    exact hApos.ne' hsum
  ·
    obtain ⟨D₀, hD₀m, hD₀F, hfin⟩ := finite_on_tate K a b ha hab
    have heq : μ (A ∩ D₀) = μ (A ∩ D) := hD₀F.measure_set_eq hDF hAm hAinv
    rw [Set.inter_comm, ← heq, Set.inter_comm]
    exact hfin

end Vol17
open scoped _root_.P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top.Vol17

end
open scoped _root_.P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top.Vol17

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) ∧
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ :=
  Vol17.main K D hD hDF a b ha hab
