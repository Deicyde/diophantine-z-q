/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem.solution
