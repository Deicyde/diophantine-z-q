/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] [Module.FaithfullyFlat k A]
    (hA : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by
  haveI : Module.Flat k A := inferInstance

  letI alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop :=
    CommRingCat.ofHom_hom _

  have h := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat fX A
  rw [← hφ] at h
  set e := h.isColimit.coconePointUniqueUpToIso (CommRingCat.pushoutCoconeIsColimit k A Γ(X, ⊤)) with he
  have hinl : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop) ≫ e.hom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤))) := by
    have := h.isColimit.comp_coconePointUniqueUpToIso_hom (CommRingCat.pushoutCoconeIsColimit k A Γ(X, ⊤))
      WalkingSpan.left
    rw [← CommRingCat.pushoutCocone_inl]
    exact this

  have hincl : Function.Bijective (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤))) := by
    have heq : ∀ a : A, Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤)) a =
        e.hom.hom (((pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
      intro a
      have := congrArg (fun f => (CommRingCat.Hom.hom f) a) hinl
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
      exact this.symm
    have hfun : (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤)) : A → A ⊗[k] Γ(X, ⊤)) =
        e.hom.hom ∘ (fun a => ((pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := funext heq
    rw [hfun]
    refine e.commRingCatIsoToRingEquiv.bijective.comp ?_
    have hA' := hA
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hA'
    exact hA'

  have hl : Function.Bijective (LinearMap.lTensor A (Algebra.linearMap k Γ(X, ⊤))) := by
    have heq : (LinearMap.lTensor A (Algebra.linearMap k Γ(X, ⊤)) : A ⊗[k] k → A ⊗[k] Γ(X, ⊤)) =
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤))) ∘ (TensorProduct.rid k A) := by
      apply funext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul,
          Algebra.TensorProduct.includeLeftRingHom_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add x y hx hy => simp only [map_add, Function.comp_apply] at hx hy ⊢; rw [hx, hy]
    rw [heq]
    exact hincl.comp (TensorProduct.rid k A).bijective

  have hφbij := (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k A (Algebra.linearMap k Γ(X, ⊤))).mp hl
  exact hφbij
