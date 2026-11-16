/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)) :
    (∀ n : ℕ, (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsCoherent ∧
      (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).IsQuasicoherent) ∧
    (∀ (n : ℕ) (U : X.Opens),
      I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))).obj U)) = ⊥) ∧
    ∃ τ : ∀ n : ℕ, OModulePresheaf.AffHom
        (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1))))
        (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))),
      (∀ (n : ℕ) (U : X.affineOpens)
        (x : (OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1),
        (τ n).app U x =
          ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1)
            ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
            (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom x) ∧
      (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
      (∀ (n : ℕ) (U : X.affineOpens),
        LinearMap.ker ((τ n).app U) =
          I ^ (n + 1) • (⊤ : Submodule R
            ((OModulePresheaf.pushforwardUnit f (g (n + 1) ≫ pullback.fst f (sR (n + 1)))).obj U.1))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback.solution
