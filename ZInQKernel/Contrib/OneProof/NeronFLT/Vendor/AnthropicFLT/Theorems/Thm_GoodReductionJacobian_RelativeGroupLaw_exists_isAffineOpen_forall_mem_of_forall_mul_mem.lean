/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective NeronModelInfra GoodReductionJacobian"

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of R))
    [IsFinite t₁] [Flat t₁] [LocallyOfFinitePresentation t₁] [Surjective t₁]
    (γ : SchemeHomOver t₁ g) (U : B.Opens) (hU : IsAffineOpen U) (S : Finset B)
    (hS : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B) (t : Spec (CommRingCat.of K) ⟶ T)
      (hx : x ≫ g = t ≫ t₁), x.base (IsLocalRing.closedPoint K) ∈ S →
      (LB.mul (t ≫ t₁) (schemeHomOverComp t rfl γ) ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem.solution
