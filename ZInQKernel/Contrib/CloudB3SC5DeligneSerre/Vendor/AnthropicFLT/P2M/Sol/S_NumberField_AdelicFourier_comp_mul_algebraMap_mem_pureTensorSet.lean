/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet (git blob 53d4e603ef62ac912239df06d399253c64566228, sha256 85699133f9d34eac59e83e0150e2455e7c2790b7da98cd913e10d02276bbb332).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField.AdelicFourier
open _root_.IsDedekindDomain
open scoped Classical SchwartzMap

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (pureTensorSet)
namespace Ws25DIL
open _root_.NumberField.AdelicFourier
open _root_.NumberField

def mulLeftLinearEquiv {A : Type*} [CommRing A] [Algebra ℝ A] (c c' : A) (h : c' * c = 1) :
    A ≃ₗ[ℝ] A where
  toFun x := c * x
  invFun x := c' * x
  map_add' x y := mul_add c x y
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]

def mulLeftHomeomorph {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃ₜ A where
  toFun x := c * x
  invFun x := c' * x
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

variable (F : Type) [Field F] [NumberField F]

theorem dil_impl {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf

  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a with hc
  set c' : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc'
  have hcc : c' * c = 1 := by rw [hc, hc', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let M : mixedEmbedding.mixedSpace F ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (mulLeftLinearEquiv c c' hcc).toContinuousLinearEquiv
  have hM : ∀ v, M v = c * v := fun v => rfl
  let g' : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g
  have hg' : ∀ v, g' v = g (c * v) := fun v => by
    show (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g) v = _
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    rfl

  set d : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a with hd
  set d' : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ with hd'
  have hdd : d' * d = 1 := by rw [hd, hd', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let Φ : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F := mulLeftHomeomorph d d' hdd
  have hΦ : (fun z => h (d * z)) = h ∘ Φ := rfl
  refine ⟨g', fun z => h (d * z), hlc.comp_continuous (continuous_const.mul continuous_id),
    by rw [hΦ]; exact hcs.comp_homeomorph Φ, ?_⟩
  funext x
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).1 = algebraMap F (InfiniteAdeleRing F) a * x.1 := rfl
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).2 = d * x.2 := rfl
  show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) a * x).1)
      * h (algebraMap F (AdeleRing (𝓞 F) F) a * x).2
    = g' (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h (d * x.2)
  rw [h1, h2, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hg']

end NumberField.AdelicFourier.Ws25DIL

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField.AdelicFourier
open _root_.IsDedekindDomain
open scoped Classical

theorem solution
    (F : Type) [Field F] [NumberField F] {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F :=
  NumberField.AdelicFourier.Ws25DIL.dil_impl F ha hf
