/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
    (R : Type u) [CommRing R] (I : Ideal R)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    (F : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x))
    (n : ℕ) (U : X.AffineZariskiSite) :
    IsPushout (α.app (op U)) ((pullback.fst f (sR n)).app U.1) (CommRingCat.ofHom (r n U))
      ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top.solution
