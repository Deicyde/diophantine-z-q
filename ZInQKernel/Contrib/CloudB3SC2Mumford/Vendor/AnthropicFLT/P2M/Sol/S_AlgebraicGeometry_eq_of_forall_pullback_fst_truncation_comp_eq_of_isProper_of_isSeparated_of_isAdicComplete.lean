/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (F F' : X ⟶ Y) (hF : F ≫ g = f) (hF' : F' ≫ g = f)
    (h : ∀ n : ℕ, Limits.pullback.fst f (sR n) ≫ F = Limits.pullback.fst f (sR n) ≫ F') :
    F = F' := by

  let p : X ⟶ pullback g g := pullback.lift F F' (by rw [hF, hF'])
  have hp₁ : p ≫ pullback.fst g g = F := pullback.lift_fst _ _ _
  have hp₂ : p ≫ pullback.snd g g = F' := pullback.lift_snd _ _ _
  let e := pullback.fst p (pullback.diagonal g)
  haveI : IsClosedImmersion (pullback.diagonal g) := IsSeparated.isClosedImmersion_diagonal
  haveI : IsClosedImmersion e := MorphismProperty.pullback_fst _ _ inferInstance

  have hfac : ∀ n : ℕ, pullback.fst f (sR n) ≫ p = (pullback.fst f (sR n) ≫ F) ≫ pullback.diagonal g := by
    intro n
    apply pullback.hom_ext
    · rw [Category.assoc, hp₁, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hp₂, Category.assoc, pullback.diagonal_snd, Category.comp_id, h n]
  have hker : ∀ n : ℕ, e.ker ≤ (pullback.fst f (sR n)).ker := by
    intro n
    have : pullback.lift (pullback.fst f (sR n)) (pullback.fst f (sR n) ≫ F) (hfac n) ≫ e = pullback.fst f (sR n) :=
      pullback.lift_fst _ _ _
    rw [← this]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : e.ker = ⊥ :=
    AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
      R I f sR hsR e.ker hker
  haveI : IsIso e := (IsClosedImmersion.isIso_iff_ker_eq_bot).mpr hbot

  have hpe : p = inv e ≫ pullback.snd p (pullback.diagonal g) ≫ pullback.diagonal g := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have k1 : p ≫ pullback.fst g g = inv e ≫ pullback.snd p (pullback.diagonal g) := by
    have := congrArg (· ≫ pullback.fst g g) hpe
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id] using this
  have k2 : p ≫ pullback.snd g g = inv e ≫ pullback.snd p (pullback.diagonal g) := by
    have := congrArg (· ≫ pullback.snd g g) hpe
    simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using this
  exact hp₁.symm.trans (k1.trans (k2.symm.trans hp₂))
