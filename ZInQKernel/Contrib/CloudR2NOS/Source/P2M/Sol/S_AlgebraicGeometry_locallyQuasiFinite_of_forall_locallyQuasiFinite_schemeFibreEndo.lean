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
  Source file    : P2M/Sol/S_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo.lean
  Source sha256  : cf4247f0328dc3c54c66eadcf8155c0196c81d5a41dff4579968a2c8e4a5a988
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

theorem solution
    {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (hfib : ∀ s : S, LocallyQuasiFinite (schemeFibreEndo f h hcomm s)) :
    LocallyQuasiFinite h := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro y
  let s : S := f.base y
  let ι : Spec (S.residueField s) ⟶ S := S.fromSpecResidueField s
  let Xs : Scheme.{u} := pullback f ι
  let π : Xs ⟶ X := pullback.fst f ι
  let hs : Xs ⟶ Xs := schemeFibreEndo f h hcomm s
  haveI : LocallyQuasiFinite hs := hfib s

  have hsq : IsPullback π hs h π := by
    refine IsPullback.of_isLimit' ⟨(schemeFibreEndo_fst f h hcomm s).symm⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun c => pullback.lift c.fst (c.snd ≫ pullback.snd f ι) ?_) ?_ ?_ ?_
    · calc c.fst ≫ f = c.fst ≫ (h ≫ f) := by rw [hcomm]
        _ = (c.fst ≫ h) ≫ f := (Category.assoc _ _ _).symm
        _ = (c.snd ≫ π) ≫ f := by rw [c.condition]
        _ = (c.snd ≫ pullback.snd f ι) ≫ ι := by rw [Category.assoc, pullback.condition, Category.assoc]
    · intro c
      exact pullback.lift_fst _ _ _
    · intro c
      apply pullback.hom_ext
      · rw [Category.assoc, schemeFibreEndo_fst, ← Category.assoc, pullback.lift_fst, c.condition]
      · rw [Category.assoc, schemeFibreEndo_snd, pullback.lift_snd]
    · intro c m hm₁ hm₂
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact hm₁
      · rw [pullback.lift_snd, ← hm₂, Category.assoc, schemeFibreEndo_snd]

  let g : Spec (X.residueField y) ⟶ Xs :=
    pullback.lift (X.fromSpecResidueField y) (Spec.map (f.residueFieldMap y))
      (by rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])
  have hg : g ≫ π = X.fromSpecResidueField y := pullback.lift_fst _ _ _
  have hcond : h.fiberι y ≫ h = h.fiberToSpecResidueField y ≫ X.fromSpecResidueField y :=
    pullback.condition
  let k : h.fiber y ⟶ Xs :=
    pullback.lift (h.fiberι y) (h.fiberToSpecResidueField y ≫ Spec.map (f.residueFieldMap y))
      (by
        calc h.fiberι y ≫ f = h.fiberι y ≫ (h ≫ f) := by rw [hcomm]
          _ = (h.fiberι y ≫ h) ≫ f := (Category.assoc _ _ _).symm
          _ = (h.fiberToSpecResidueField y ≫ X.fromSpecResidueField y) ≫ f := by rw [hcond]
          _ = (h.fiberToSpecResidueField y ≫ Spec.map (f.residueFieldMap y)) ≫ ι := by
              rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc])
  have hk : k ≫ π = h.fiberι y := pullback.lift_fst _ _ _
  have hmid : k ≫ hs = h.fiberToSpecResidueField y ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, schemeFibreEndo_fst, ← Category.assoc, hk, hcond, Category.assoc, hg]
    · rw [Category.assoc, schemeFibreEndo_snd, pullback.lift_snd, Category.assoc, pullback.lift_snd]
  have hbig : IsPullback (k ≫ π) (h.fiberToSpecResidueField y) h (g ≫ π) := by
    rw [hk, hg]
    exact IsPullback.of_hasPullback h (X.fromSpecResidueField y)
  have hfinal : IsPullback k (h.fiberToSpecResidueField y) hs g := IsPullback.of_right hbig hmid hsq
  exact MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hfinal (hfib s)
end S_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
