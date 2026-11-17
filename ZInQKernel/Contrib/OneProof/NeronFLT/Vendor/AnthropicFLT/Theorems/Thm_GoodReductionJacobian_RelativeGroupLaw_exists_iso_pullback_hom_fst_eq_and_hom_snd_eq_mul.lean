/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
    {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    ∃ σ : pullback t g ≅ pullback t g,
      σ.hom ≫ pullback.fst t g = pullback.fst t g ∧
      σ.hom ≫ pullback.snd t g =
        (L.mul (pullback.fst t g ≫ t) ⟨pullback.fst t g ≫ a.1, by rw [Category.assoc, a.2]⟩
          ⟨pullback.snd t g, pullback.condition.symm⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.solution
