/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((LB.mul (pullback.snd g (B.fromSpecResidueField s₀ ≫ g) ≫ (B.fromSpecResidueField s₀ ≫ g))
          ⟨pullback.fst g (B.fromSpecResidueField s₀ ≫ g), pullback.condition⟩
          (schemeHomOverComp (pullback.snd g (B.fromSpecResidueField s₀ ≫ g)) rfl
            (⟨B.fromSpecResidueField s₀, rfl⟩ :
              SchemeHomOver (B.fromSpecResidueField s₀ ≫ g) g))).1.base ⁻¹' ((U : Set B)ᶜ))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.solution
