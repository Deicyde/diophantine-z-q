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
  Source file    : Definitions/Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism.lean
  Source sha256  : 71f363e373ebf10e8abecac00d781bd8df375c032e030005c0976f6cdbf8644d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T2×16, T4×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

namespace NeronModelInfra
r2nos_namespace_dual

section ValueFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (χ : SchemeHomOver f f) (hχ : χ.1 = 𝟙 X) :
    (genericFibreRestrict R K f f χ).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ]
  · simp [genericFibreRestrict, pullback.lift_snd]

theorem genericFibreRestrict_val_eq_comp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver g e)
    (hχ : χ.1 = φ.1 ≫ ψ.1) :
    (genericFibreRestrict R K e g χ).1 =
      (genericFibreRestrict R K f g φ).1 ≫ (genericFibreRestrict R K e f ψ).1 := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp [genericFibreRestrict, pullback.lift_snd]

end ValueFunctoriality

section MinimalModelLemma

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X : Scheme.{u}}

theorem neronModel_end_eq_id_of_restrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (hN : NeronUniqueExtension R K f) (hsf : Smooth f) (w : SchemeHomOver f f)
    (hw : (genericFibreRestrict R K f f w).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K))) :
    w.1 = 𝟙 X := by
  have hres : genericFibreRestrict R K f f w =
      genericFibreRestrict R K f f ⟨𝟙 X, Category.id_comp f⟩ := by
    apply Subtype.ext
    rw [hw, genericFibreRestrict_val_eq_id R K f ⟨𝟙 X, Category.id_comp f⟩ rfl]
  have hwid : w = (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) :=
    (hN X f hsf).1 hres
  exact congrArg Subtype.val hwid

end MinimalModelLemma

section TwoModels

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X X' : Scheme.{u}}

theorem neronTwoModels_extension_unique
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    {u₁ u₂ : SchemeHomOver f f'}
    (h : genericFibreRestrict R K f' f u₁ = genericFibreRestrict R K f' f u₂) :
    u₁ = u₂ :=
  (hNf' X f hsf).1 h

theorem neronTwoModels_existsUnique_homExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f', genericFibreRestrict R K f' f u = uK :=
  (hNf' X f hsf).existsUnique uK

theorem neronTwoModels_comp_eq_id
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hsf : Smooth f)
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    {vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} {v : SchemeHomOver f' f}
    (hu : genericFibreRestrict R K f' f u = uK)
    (hv : genericFibreRestrict R K f f' v = vK) :
    u.1 ≫ v.1 = 𝟙 X := by
  have hcomp : (u.1 ≫ v.1) ≫ f = f := by rw [Category.assoc, v.2, u.2]
  have hval : (genericFibreRestrict R K f f ⟨u.1 ≫ v.1, hcomp⟩).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
    rw [genericFibreRestrict_val_eq_comp R K f' f f u v ⟨u.1 ≫ v.1, hcomp⟩ rfl, hu, hv]
    exact huv
  exact neronModel_end_eq_id_of_restrict_val_eq_id R K f hNf hsf ⟨u.1 ≫ v.1, hcomp⟩ hval

theorem neronTwoModels_exists_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, hu⟩ := (hNf' X f hsf).2 uK
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨u, v, hu, hv, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩

theorem neronTwoModels_existsUnique_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, v, hu, hv, huvId, hvuId⟩ :=
    neronTwoModels_exists_isoExtension hNf hNf' hsf hsf' uK vK huv hvu
  refine ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

theorem neronTwoModels_isoExtension_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 := by
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨⟨v.1, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩⟩

theorem neronTwoModels_existsUnique_isoExtension_of_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) [IsIso uK.1] :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        (genericFibreRestrict R K f f' v).1 = inv uK.1 ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  have hvKmem : inv uK.1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f' (specGenericFibreInclusion R K) :=
    (IsIso.inv_comp_eq uK.1).mpr uK.2.symm
  obtain ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, -⟩ :=
    neronTwoModels_existsUnique_isoExtension hNf hNf' hsf hsf' uK ⟨inv uK.1, hvKmem⟩
      (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1)
  refine ⟨u, ⟨hu, v, congrArg Subtype.val hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

end TwoModels

section BundleForm

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X X' : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.exists_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_exists_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.existsUnique_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_existsUnique_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.isoExtension_isIso
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 :=
  neronTwoModels_isoExtension_isIso h.neronMapping h'.neronMapping h.smooth h'.smooth
    vK huv hvu hu

end BundleForm


end NeronModelInfra
















end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
