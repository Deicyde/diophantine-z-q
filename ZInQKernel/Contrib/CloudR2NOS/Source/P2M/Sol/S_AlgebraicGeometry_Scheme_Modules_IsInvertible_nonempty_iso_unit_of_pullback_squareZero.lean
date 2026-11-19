/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero.lean
  Source sha256  : 0d233d6e8ad4bf0564e2ae9e1dffc5ce2eb7d828d02acb0699ef7b62a521b6d0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 32000000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
r2nos_namespace_dual

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

set_option autoImplicit false

noncomputable section

private theorem proj_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Projective S M] :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.Projective R M := by
  letI : Module R M := Module.compHom M e.toRingHom
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.of_ringEquiv e.symm
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  have slEq : M ≃ₛₗ[(e.symm : S →+* R)] M :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl,
      map_smul' := fun s m => by
        simp only [id]
        change s • m = (e (e.symm s)) • m
        rw [e.apply_symm_apply] }
  exact Module.Projective.of_equiv slEq

private theorem fin_of_surj {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Finite S M] :
    letI : Module R M := Module.compHom M f
    Module.Finite R M := by
  letI : Module R M := Module.compHom M f
  obtain ⟨s, hs⟩ := ‹Module.Finite S M›.1
  refine ⟨s, ?_⟩
  rw [eq_top_iff]; intro m _
  have hm : m ∈ Submodule.span S (↑s : Set M) := hs ▸ Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · intro x hx; exact Submodule.subset_span hx
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    obtain ⟨r, hr⟩ := hf a
    have heq : a • x = r • x := by
      show a • x = f r • x; rw [hr]
    rw [heq]; exact Submodule.smul_mem _ r hx

theorem solution
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (L : (Spec (CommRingCat.of B)).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h : Nonempty ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj L
          ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by

  haveI hIso := Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial
    (R := CommRingCat.of B) L hL.exists_trivialization

  let eL := @asIso _ _ _ _ _ hIso

  have hPtop := Scheme.Modules.projective_sections_of_locallyTrivial (X := Spec (.of B)) L
    hL.exists_trivialization ⟨⊤, isAffineOpen_top _⟩
  have hFtop := Scheme.Modules.finite_sections_of_locallyTrivial (X := Spec (.of B)) L
    hL.exists_trivialization ⟨⊤, isAffineOpen_top _⟩
  let gsi : B ≃+* ↑Γ(Spec (CommRingCat.of B), (⊤ : (Spec (.of B)).Opens)) :=
    (StructureSheaf.globalSectionsIso B).commRingCatIsoToRingEquiv
  haveI hQproj : Module.Projective B
      ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
    have := proj_of_ringEquiv gsi (↑Γ(L, (⊤ : (Spec (.of B)).Opens)))
    exact this
  haveI hQfin : Module.Finite B
      ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
    have := fin_of_surj gsi.toRingHom gsi.surjective (↑Γ(L, (⊤ : (Spec (.of B)).Opens)))
    exact this

  let φ := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have e5 :=
    (tilde.pullbackSpecIso φ ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L)).symm ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapIso eL ≪≫
    h.some ≪≫
    (tildeSelf (R := CommRingCat.of (B ⧸ I))).symm

  have e6 := (tilde.fullyFaithfulFunctor (R := CommRingCat.of (B ⧸ I))).preimageIso e5

  let e7 : ((B ⧸ I) ⊗[B] ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L))
      ≃ₗ[B ⧸ I] (B ⧸ I) ⊗[B] B :=
    e6.toLinearEquiv.trans (TensorProduct.AlgebraTensorModule.rid B (B ⧸ I) (B ⧸ I)).symm

  obtain ⟨eQB⟩ := Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    I hI (↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L)) B e7

  exact ⟨eL.symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso (LinearEquiv.toModuleIso eQB) ≪≫
    tildeSelf (R := CommRingCat.of B)⟩

end
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
