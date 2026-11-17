/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq (git blob e5ba6476e5fafd2503caf7fbadb9821242327b05, sha256 3605668244477bf8902ea03fce90466f357d32d7548a4eb2b6734d2f5f971d35).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors NNReal ENNReal

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing RingOfIntegers.coe_ne_zero_iff)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (fourierIntegral fourierIntegral_def fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply setIntegral_addChar_mul_eq_ite_of_isCompact measure_setOf_forall_addChar_finitePart_mul_eq_one forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one)
namespace Ws25FinInv
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]





section Algebra

variable (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

theorem addChar_neg_eq_one_iff (x : (FiniteAdeleRing (𝓞 F) F)) : ψf (-x) = 1 ↔ ψf x = 1 := by
  have key : ψf (-x) * ψf x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    rw [h, mul_one] at key
    exact key

def annSubgroup (a : (FiniteAdeleRing (𝓞 F) F)) : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {w | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (a * w * z) = 1}
  zero_mem' := by
    intro z _
    rw [mul_zero, zero_mul, AddChar.map_zero_eq_one]
  add_mem' := by
    intro x y hx hy z hz
    rw [mul_add, add_mul, AddChar.map_add_eq_mul, hx z hz, hy z hz, one_mul]
  neg_mem' := by
    intro x hx z hz
    rw [mul_neg, neg_mul, addChar_neg_eq_one_iff]
    exact hx z hz

theorem mem_annSubgroup (a w : (FiniteAdeleRing (𝓞 F) F)) :
    w ∈ annSubgroup ψf a ↔ ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (a * w * z) = 1 := Iff.rfl

theorem coe_annSubgroup (a : (FiniteAdeleRing (𝓞 F) F)) :
    (annSubgroup ψf a : Set (FiniteAdeleRing (𝓞 F) F)) = (fun x => a * x) ⁻¹' {w | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1} := rfl

theorem coe_annSubgroup_one :
    (annSubgroup ψf 1 : Set (FiniteAdeleRing (𝓞 F) F)) = {w | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1} := by
  ext w
  simp only [SetLike.mem_coe, mem_annSubgroup, one_mul, Set.mem_setOf_eq]

theorem preimage_mul_eq_image_mul {a b : (FiniteAdeleRing (𝓞 F) F)} (hab : a * b = 1) (E : Set (FiniteAdeleRing (𝓞 F) F)) :
    (fun x => a * x) ⁻¹' E = (fun x => b * x) '' E := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨a * x, hx, by rw [← mul_assoc, hba, one_mul]⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, hab, one_mul]

theorem mul_right_injective_of_mul_eq_one {a b : (FiniteAdeleRing (𝓞 F) F)} (hab : a * b = 1) :
    Function.Injective (fun x : (FiniteAdeleRing (𝓞 F) F) => a * x) := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  intro x y hxy
  have h := congrArg (fun t => b * t) hxy
  simp only [← mul_assoc, hba, one_mul] at h
  exact h

end Algebra

section Measure

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [ν.IsAddHaarMeasure] in

theorem fourierIntegral_finset_sum_smul (s : Finset F) (c : F → ℂ) (g : F → (FiniteAdeleRing (𝓞 F) F) → ℂ) (w : (FiniteAdeleRing (𝓞 F) F))
    (hint : ∀ k ∈ s, Integrable (fun v => ψf (-(v * w)) * g k v) ν) :
    fourierIntegral ψf ν (∑ k ∈ s, c k • g k) w = ∑ k ∈ s, c k * fourierIntegral ψf ν (g k) w := by
  simp only [fourierIntegral_def]
  have hpt : (fun v => ψf (-(v * w)) * (∑ k ∈ s, c k • g k) v)
      = fun v => ∑ k ∈ s, c k * (ψf (-(v * w)) * g k v) := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hpt, integral_finsetSum s (fun k hk => (hint k hk).const_mul (c k))]
  exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)

theorem integrable_kernel_mul_indicator (hcont : Continuous ψf) {E : Set (FiniteAdeleRing (𝓞 F) F)} (hE : IsCompact E)
    {φ : (FiniteAdeleRing (𝓞 F) F) → ℂ} (hφ : Continuous φ) (w : (FiniteAdeleRing (𝓞 F) F)) :
    Integrable (fun v => ψf (-(v * w)) * E.indicator φ v) ν := by
  have hrw : (fun v => ψf (-(v * w)) * E.indicator φ v)
      = E.indicator (fun v => ψf (-(v * w)) * φ v) := by
    funext v
    exact (Set.indicator_mul_right E (fun v => ψf (-(v * w))) φ).symm
  rw [hrw, integrable_indicator_iff hE.isClosed.measurableSet]
  have hk : Continuous fun v : (FiniteAdeleRing (𝓞 F) F) => ψf (-(v * w)) :=
    hcont.comp ((continuous_id.mul continuous_const).neg)
  exact ContinuousOn.integrableOn_compact hE (hk.mul hφ).continuousOn

def mulEquiv (a b : (FiniteAdeleRing (𝓞 F) F)) (hab : a * b = 1) : (FiniteAdeleRing (𝓞 F) F) ≃+ (FiniteAdeleRing (𝓞 F) F) where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' x y := mul_add a x y

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv (a b : (FiniteAdeleRing (𝓞 F) F)) (hab : a * b = 1) : ⇑(mulEquiv a b hab) = fun x => a * x := rfl

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv_symm (a b : (FiniteAdeleRing (𝓞 F) F)) (hab : a * b = 1) :
    ⇑(mulEquiv a b hab).symm = fun x => b * x := rfl

theorem exists_measure_preimage_mul (a b : (FiniteAdeleRing (𝓞 F) F)) (hab : a * b = 1) :
    ∃ c : ℝ≥0∞, ∀ E : Set (FiniteAdeleRing (𝓞 F) F), IsCompact E → ν ((fun x => a * x) ⁻¹' E) = c * ν E := by
  have he : Continuous (mulEquiv a b hab) := by
    rw [coe_mulEquiv]; exact continuous_const.mul continuous_id
  have hes : Continuous (mulEquiv a b hab).symm := by
    rw [coe_mulEquiv_symm]; exact continuous_const.mul continuous_id
  haveI := AddEquiv.isAddHaarMeasure_map ν (mulEquiv a b hab) he hes
  refine ⟨Measure.addHaarScalarFactor (Measure.map (mulEquiv a b hab) ν) ν, fun E hE => ?_⟩
  have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
    (Measure.map (mulEquiv a b hab) ν) ν (s := E) (by rw [hE.isClosed.closure_eq]; exact hE)
  rw [Measure.map_apply he.measurable hE.isClosed.measurableSet, ENNReal.smul_def, smul_eq_mul] at h
  exact h

end Measure

section Main

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)



theorem fourierIntegral_indicator_coset_eq_indicator (hcont : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    fourierIntegral ψf ν (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1)
      = (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)).indicator
          (fun w => ((ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) * ψf (-((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k * w))) := by
  funext w
  rw [fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply F ν hcont d hd k w]
  by_cases hw : ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * w * z) = 1
  · rw [if_pos hw, mul_one, mul_comm,
      Set.indicator_of_mem (show w ∈ (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)) from hw)]
  · rw [if_neg hw, mul_zero,
      Set.indicator_of_notMem (show w ∉ (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)) from hw)]

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem isCompact_annSubgroup (hAc : IsCompact {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1})
    {a b : (FiniteAdeleRing (𝓞 F) F)} (hab : a * b = 1) : IsCompact (annSubgroup ψf a : Set (FiniteAdeleRing (𝓞 F) F)) := by
  rw [coe_annSubgroup, preimage_mul_eq_image_mul hab]
  exact hAc.image (continuous_const.mul continuous_id)

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem forall_annSubgroup_iff_neg_mem
    (hbi : ∀ u : (FiniteAdeleRing (𝓞 F) F), (∀ w : (FiniteAdeleRing (𝓞 F) F), (∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ (integralFiniteAdeles (𝓞 F) F))
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : (FiniteAdeleRing (𝓞 F) F)) :
    (∀ w ∈ annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)), ψf (-((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * w) = 1) ↔ -y ∈ ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hba : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) = 1 := by rw [mul_comm]; exact hab

  have h1 : (∀ w ∈ annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)), ψf (-((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * w) = 1)
      ↔ (∀ w : (FiniteAdeleRing (𝓞 F) F), (∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1) → ψf (((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ * w) = 1) := by
    constructor
    · intro h w hw
      have hmem : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ * w ∈ annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) := by
        rw [mem_annSubgroup]
        intro z hz
        rw [← mul_assoc, hab, one_mul]
        exact hw z hz
      have h' := h _ hmem
      rw [neg_mul, addChar_neg_eq_one_iff, ← mul_assoc] at h'
      exact h'
    · intro h w hw
      rw [mem_annSubgroup] at hw
      have h' := h ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * w) hw
      rw [neg_mul, addChar_neg_eq_one_iff]
      have e : ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ * ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * w) = ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * w := by
        rw [mul_assoc, ← mul_assoc ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹), hba, one_mul]
      rw [e] at h'
      exact h'
  rw [h1, hbi]

  constructor
  · intro hu
    refine ⟨-(((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹), fun v => neg_mem (hu v), ?_⟩
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * -(((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹) = -y
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * (((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹) = (algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y := by
      rw [mul_comm ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y), ← mul_assoc, hab, one_mul]
    rw [mul_neg, e]
    ring
  · rintro ⟨z, hz, hzy⟩
    have e : ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ = -z := by
      have hzy' : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z = -y := hzy
      have hy : y = -((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) := by rw [hzy', neg_neg]
      rw [hy]
      have : ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + -((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z)) = -((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) := by ring
      rw [this, neg_mul, mul_comm ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) z, mul_assoc, hab, mul_one]
    rw [e]
    exact fun v => neg_mem (hz v)

theorem measure_coset_mul_measure_annSubgroup
    (hAc : IsCompact {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1})
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) * ν (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F))
      = ν (integralFiniteAdeles (𝓞 F) F) * ν {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  obtain ⟨c, hc⟩ := exists_measure_preimage_mul ν ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹) hab
  have hO_cpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles (K := F)

  have hB_cpt : IsCompact ((fun z => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) '' (integralFiniteAdeles (𝓞 F) F)) :=
    hO_cpt.image (continuous_const.mul continuous_id)
  have hS_eq : ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) = (fun b => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + b) '' ((fun z => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) '' (integralFiniteAdeles (𝓞 F) F)) :=
    (Set.image_image (fun b => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + b) (fun z => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) (integralFiniteAdeles (𝓞 F) F)).symm
  have hS : ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) = ν ((fun z => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) '' (integralFiniteAdeles (𝓞 F) F)) := by
    rw [hS_eq, Set.image_add_left, measure_preimage_add]

  have hO : ν (integralFiniteAdeles (𝓞 F) F) = c * ν ((fun z => (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * z) '' (integralFiniteAdeles (𝓞 F) F)) := by
    have h := hc _ hB_cpt
    rwa [Set.preimage_image_eq _ (mul_right_injective_of_mul_eq_one hab)] at h

  have hA : ν (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F))
      = c * ν {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1} := by
    rw [coe_annSubgroup]
    exact hc _ hAc
  rw [hS, hA, hO]
  ring

theorem fourierIntegral_fourierIntegral_indicator_coset (hcont : Continuous ψf)
    (hAc : IsCompact {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1})
    (hbi : ∀ u : (FiniteAdeleRing (𝓞 F) F), (∀ w : (FiniteAdeleRing (𝓞 F) F), (∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ (integralFiniteAdeles (𝓞 F) F))
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : (FiniteAdeleRing (𝓞 F) F)) :
    fourierIntegral ψf ν (fourierIntegral ψf ν (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1)) y
      = ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) * ((ν {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1}).toReal : ℂ)
          * ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 (-y) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hKc : IsCompact (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)) :=
    isCompact_annSubgroup ψf hAc hab
  have hKm : MeasurableSet (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hKc.isClosed.measurableSet

  have h1 : fourierIntegral ψf ν (fourierIntegral ψf ν (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1)) y
      = ((ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * ∫ w in (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)), ψf (-((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y) * w) ∂ν := by
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k, fourierIntegral_def,
      ← integral_const_mul, ← integral_indicator hKm]
    congr 1
    funext w
    by_cases hw : w ∈ (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F))
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, mul_left_comm, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]

  have h2 := setIntegral_addChar_mul_eq_ite_of_isCompact F ν ψf (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F))) hKc
    (-((algebraMap F (FiniteAdeleRing (𝓞 F) F)) k + y))

  have h3 : ((ν ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) * ((ν (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F))).toReal : ℂ)
      = ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) * ((ν {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1}).toReal : ℂ) := by
    have h := congrArg (fun t : ℝ≥0∞ => ((t.toReal : ℝ) : ℂ))
      (measure_coset_mul_measure_annSubgroup ν ψf hAc d hd k)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul] at h
    exact h
  rw [h1, h2]
  by_cases hy : -y ∈ ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
  · rw [if_pos ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mpr hy),
      Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    exact h3
  · rw [if_neg (fun h => hy ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mp h)),
      Set.indicator_of_notMem hy, mul_zero, mul_zero]

theorem fourierIntegral_fourierIntegral_eq (hcont : Continuous ψf)
    (hAc : IsCompact {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1})
    (hbi : ∀ u : (FiniteAdeleRing (𝓞 F) F), (∀ w : (FiniteAdeleRing (𝓞 F) F), (∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ (integralFiniteAdeles (𝓞 F) F))
    {h : (FiniteAdeleRing (𝓞 F) F) → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (y : (FiniteAdeleRing (𝓞 F) F)) :
    fourierIntegral ψf ν (fourierIntegral ψf ν h) y
      = ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) * ((ν {w : (FiniteAdeleRing (𝓞 F) F) | ∀ z ∈ (integralFiniteAdeles (𝓞 F) F), ψf (w * z) = 1}).toReal : ℂ) * h (-y) := by
  obtain ⟨d, hd, s, c, rfl⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hO_cpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles (K := F)
  have hS_cpt : ∀ k : F, IsCompact ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) := fun k =>
    hO_cpt.image (continuous_const.add (continuous_const.mul continuous_id))

  have hinner : fourierIntegral ψf ν (∑ k ∈ s, c k • ((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1)
      = ∑ k ∈ s, c k • fourierIntegral ψf ν (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) := by
    funext w
    rw [fourierIntegral_finset_sum_smul ν ψf s c _ w
      (fun k _ => integrable_kernel_mul_indicator ν ψf hcont (hS_cpt k) continuous_one w)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hKc : IsCompact (annSubgroup ψf ((algebraMap F (FiniteAdeleRing (𝓞 F) F)) (d : F)) : Set (FiniteAdeleRing (𝓞 F) F)) :=
    isCompact_annSubgroup ψf hAc hab
  have hint : ∀ k ∈ s, Integrable
      (fun w => ψf (-(w * y)) * fourierIntegral ψf ν (((fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w) ν := by
    intro k _
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k]
    exact integrable_kernel_mul_indicator ν ψf hcont hKc
      (continuous_const.mul (hcont.comp ((continuous_const.mul continuous_id).neg))) y
  rw [hinner, fourierIntegral_finset_sum_smul ν ψf s c _ y hint]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fourierIntegral_fourierIntegral_indicator_coset ν ψf hcont hAc hbi d hd k y]
  ring

end Main

end NumberField.AdelicFourier.Ws25FinInv

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (y : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) y
      = ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
          * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2) * h (-y) := by

  have happly : ∀ w : FiniteAdeleRing (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) w
        = ψ (0, w) := fun w => rfl
  have hcont : Continuous
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
    (continuous_congr happly).mpr (hψ.continuous.comp (continuous_const.prodMk continuous_id))
  have hset : {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (w * z) = 1}
      = {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by
    simp only [happly]
  have hAc := (isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one F hψ hψ_inf).1
  have hvol := measure_setOf_forall_addChar_finitePart_mul_eq_one F ν hψ hψ_inf
  have hbi := forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles F hψ hψ_inf
  have hmain := NumberField.AdelicFourier.Ws25FinInv.fourierIntegral_fourierIntegral_eq ν
    (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
    hcont (by rw [hset]; exact hAc) (by simpa only [happly] using hbi) hlc hcs y
  rw [hmain, hset, hvol, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  push_cast
  ring
