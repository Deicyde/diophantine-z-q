/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles (git blob 702ef131f2fc0f44cee4318f14c6754b4533dee3, sha256 2016e14d909c879e401610a2bd3f2f4110b080b81a29b7bea153a617ede35875).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.Topology.LocallyConstant.Algebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    IsLocallyConstant (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      ∧ HasCompactSupport (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := by
  set S := (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F with hSdef
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hS : S = (fun y : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) ⁻¹' integralFiniteAdeles (𝓞 F) F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)
        ∈ integralFiniteAdeles (𝓞 F) F
      rwa [add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    · intro hy
      refine ⟨_, hy, ?_⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = y
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul, add_sub_cancel]
  have hopen : IsOpen S := by
    rw [hS]
    exact (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have hcpt : IsCompact S :=
    (isCompact_integralFiniteAdeles F).image (continuous_const.add (continuous_const.mul continuous_id))
  have hclopen : IsClopen S := ⟨hcpt.isClosed, hopen⟩
  refine ⟨?_, HasCompactSupport.intro hcpt fun x hx => Set.indicator_of_notMem hx _⟩
  rw [← LocallyConstant.coe_charFn ℂ hclopen]
  exact (LocallyConstant.charFn ℂ hclopen).isLocallyConstant
