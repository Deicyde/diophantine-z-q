/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen.lean
  Source sha256  : 6869c246060ecefd17dbb6169a8b154954f16d1acd8018a45dd8ce15a605f154
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

universe u

theorem solution
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f) W
    ∃ ε : ∀ (V : A.Opens) (_ : IsAffineOpen V),
        Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
      (∀ (V : A.Opens) (hV : IsAffineOpen V),
          IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
          ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
      (∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
          ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h) ∧
      (∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
          (s : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
            ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map
              (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s)) := by

  let SKH := Spec.map (CommRingCat.ofHom (algebraMap K H))
  let P := pullback f SKH
  let p₁ := pullback.fst f SKH
  let p₂ := pullback.snd f SKH
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI instKP : ∀ W : P.Opens, Algebra K Γ(P, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ f) W
  letI instHP : ∀ W : P.Opens, Algebra H Γ(P, W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom p₂ W

  haveI towerP : ∀ W : P.Opens, IsScalarTower K H Γ(P, W) := by
    intro W
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    show ((p₁ ≫ f).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom k) =
      (p₂.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom (algebraMap K H k))
    have h1 : (p₁ ≫ f).appLE ⊤ W le_top = (p₂ ≫ SKH).appLE ⊤ W le_top := by
      simp only [p₁, p₂, pullback.condition]
    rw [h1, ← Scheme.Hom.appLE_comp_appLE p₂ SKH ⊤ ⊤ W le_top le_top]
    show (p₂.appLE ⊤ W le_top).hom ((SKH.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom k)) = _
    congr 1
    have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K H))
    have h3 : SKH.appLE ⊤ ⊤ le_top = SKH.appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [h3]
    exact (congrArg (fun φ => φ.hom k) h2).symm

  have key : ∀ (V : A.Opens) (hV : IsAffineOpen V),
      ∃ ε : Γ(P, p₁ ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H,
        (∀ a : Γ(A, V), ε ((p₁.app V).hom a) = a ⊗ₜ[K] (1 : H)) ∧
        (∀ h : H, ε ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h) := by
    intro V hV
    obtain ⟨e, he⟩ := Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen f V hV H
    let ε : Γ(P, p₁ ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H :=
      ((e.restrictScalars K).symm).trans (Algebra.TensorProduct.comm K H Γ(A, V))
    refine ⟨ε, fun a => ?_, fun h => ?_⟩
    · show Algebra.TensorProduct.comm K H Γ(A, V) (e.symm ((p₁.app V).hom a)) = a ⊗ₜ[K] 1
      rw [← he a, e.symm_apply_apply, Algebra.TensorProduct.comm_tmul]
    · show Algebra.TensorProduct.comm K H Γ(A, V) (e.symm (algebraMap H Γ(P, p₁ ⁻¹ᵁ V) h)) = 1 ⊗ₜ[K] h
      rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.comm_tmul]
  choose ε hε₁ hε₂ using key
  haveI : IsAffineHom p₁ := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  refine ⟨ε, fun V hV => hV.preimage p₁, fun V hV a => hε₁ V hV a, fun V hV h => hε₂ V hV h, ?_⟩

  intro V V' hV hV' hle s
  obtain ⟨t, rfl⟩ := (ε V hV).symm.surjective s
  rw [AlgEquiv.apply_symm_apply]

  let F₁ : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H :=
    Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H)
  let res : Γ(P, p₁ ⁻¹ᵁ V) →ₐ[K] Γ(P, p₁ ⁻¹ᵁ V') := Scheme.TwoAffineOpenCover.restrictAlgHom (p₁ ≫ f) (p₁.preimage_mono hle)
  let F₂ : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H :=
    ((ε V' hV').toAlgHom.comp res).comp (ε V hV).symm.toAlgHom
  have hF : F₁ = F₂ := by
    apply Algebra.TensorProduct.ext'
    intro a h
    show Algebra.TensorProduct.map _ _ (a ⊗ₜ[K] h) = ε V' hV' (res ((ε V hV).symm (a ⊗ₜ[K] h)))
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hsplit : a ⊗ₜ[K] h = (a ⊗ₜ[K] (1 : H)) * ((1 : Γ(A, V)) ⊗ₜ[K] h) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, ← hε₁ V hV a, ← hε₂ V hV h, ← map_mul, AlgEquiv.symm_apply_apply, map_mul, map_mul]
    have hr₁ : res ((p₁.app V).hom a) = (p₁.app V').hom ((A.presheaf.map (homOfLE hle).op).hom a) := by
      show (p₁.appLE V (p₁ ⁻¹ᵁ V') (p₁.preimage_mono hle)).hom a = (A.presheaf.map (homOfLE hle).op ≫ p₁.app V').hom a
      rw [Scheme.Hom.app_eq_appLE p₁ (U := V'), Scheme.Hom.map_appLE]
    have hr₂ : res ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h)) =
        (p₂.appLE ⊤ (p₁ ⁻¹ᵁ V') le_top).hom ((Scheme.ΓSpecIso (.of H)).inv.hom h) := by
      show (P.presheaf.map (homOfLE (p₁.preimage_mono hle)).op).hom ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ V) le_top).hom _) = _
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    rw [hr₁, hr₂, hε₁ V' hV', hε₂ V' hV', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  exact congrArg (fun F : Γ(A, V) ⊗[K] H →ₐ[K] Γ(A, V') ⊗[K] H => F t) hF
end S_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
