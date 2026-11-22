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
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom.lean
  Source sha256  : 13b0e49f6cb22d14ec842082122caf7b5770b57a83e200dd819a4fe4883a2d39
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
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

universe u

theorem solution
    {X Y Y' : Scheme.{u}} (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (z : X) (hzU : z ∈ U)
    [X.IsGermInjectiveAt z]
    (β : Y' ⟶ Y) [LocallyOfFiniteType β]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y) (ℓ : Spec (CommRingCat.of O) ⟶ Y') (hℓ : ℓ ≫ β = ℓ₀)
    (φ : CommRingCat.of O ⟶ X.presheaf.stalk z) [IsLocalHom φ.hom]
    (hφ : Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α) :
    ∃ (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U') (α' : (U' : Scheme.{u}) ⟶ Y'),
      α' ≫ β = X.homOfLE hU' ≫ α ∧ α'.base ⟨z, hzU'⟩ = ℓ.base (IsLocalRing.closedPoint O) := by

  haveI : (U : Scheme.{u}).IsGermInjectiveAt (⟨z, hzU⟩ : ↥U) := by
    have hzz : U.ι.base (⟨z, hzU⟩ : ↥U) = z := rfl
    exact (isGermInjectiveAt_iff_of_isOpenImmersion (f := U.ι) (x := (⟨z, hzU⟩ : ↥U))).mp (by rw [hzz]; infer_instance)

  let w : Spec ((U : Scheme.{u}).presheaf.stalk ⟨z, hzU⟩) ⟶ Y' := Spec.map (U.ι.stalkMap ⟨z, hzU⟩) ≫ Spec.map φ ≫ ℓ
  have hUfrom : Spec.map (U.ι.stalkMap ⟨z, hzU⟩) ≫ U.fromSpecStalkOfMem z hzU = (U : Scheme.{u}).fromSpecStalk ⟨z, hzU⟩ := by
    simp only [Scheme.Opens.fromSpecStalkOfMem, Spec.map_inv]
    exact IsIso.hom_inv_id_assoc _ _
  have hw : w ≫ β = (U : Scheme.{u}).fromSpecStalk ⟨z, hzU⟩ ≫ α := by
    simp only [w, Category.assoc, hℓ]
    erw [hφ, ← Category.assoc, hUfrom]
  obtain ⟨W, hzW, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' α β w hw
  have hzW' : z ∈ U.ι ''ᵁ W := (Scheme.Opens.mem_ι_image_iff (x := (⟨z, hzU⟩ : ↥U))).mpr hzW

  refine ⟨U.ι ''ᵁ W, Scheme.Opens.ι_image_le U W, hzW', (U.ι.isoImage W).inv ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg₂, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
  ·
    have hpt : ((U.ι.isoImage W).inv ≫ g).base ⟨z, hzW'⟩ = g.base ⟨⟨z, hzU⟩, hzW⟩ := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      have h1 : ((U.ι.isoImage W).inv ≫ W.ι).base ⟨z, hzW'⟩ = ⟨z, hzU⟩ := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.isoImage_inv_ι]
        rfl
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1]
      rfl
    rw [hpt]

    have h2 : g.base ⟨⟨z, hzU⟩, hzW⟩ = w.base (IsLocalRing.closedPoint _) := by
      have := congrArg (fun k => k.base (IsLocalRing.closedPoint ((U : Scheme.{u}).presheaf.stalk ⟨z, hzU⟩))) hg₁
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]
      congr 1
      have h4 : (W.fromSpecStalkOfMem ⟨z, hzU⟩ hzW ≫ W.ι).base (IsLocalRing.closedPoint _) = ⟨z, hzU⟩ := by
        rw [Scheme.Opens.fromSpecStalkOfMem_ι]; exact Scheme.fromSpecStalk_closedPoint
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h4]
      rfl
    rw [h2]
    simp only [w, Scheme.Hom.comp_apply]
    congr 1
    have e1 : (Spec.map (U.ι.stalkMap ⟨z, hzU⟩)).base
        (IsLocalRing.closedPoint ((U : Scheme.{u}).presheaf.stalk ⟨z, hzU⟩)) = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint (U.ι.stalkMap ⟨z, hzU⟩).hom
    have e2 : (Spec.map φ).base (IsLocalRing.closedPoint (X.presheaf.stalk z)) = IsLocalRing.closedPoint O :=
      @IsLocalRing.comap_closedPoint _ _ _ _ _ _ φ.hom ‹_›
    rw [e1]
    exact e2
end S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
