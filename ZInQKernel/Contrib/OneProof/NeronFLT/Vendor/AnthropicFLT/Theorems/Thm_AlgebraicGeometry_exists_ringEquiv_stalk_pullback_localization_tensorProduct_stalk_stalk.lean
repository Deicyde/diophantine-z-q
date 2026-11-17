/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p))))) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.solution
