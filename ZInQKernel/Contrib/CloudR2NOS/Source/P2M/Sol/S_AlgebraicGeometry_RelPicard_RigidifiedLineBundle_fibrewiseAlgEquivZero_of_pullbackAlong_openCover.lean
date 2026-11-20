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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover.lean
  Source sha256  : edee6c49d5be9fe23feaf86d0bd00012684bba88e9427efa01e3e5f0e9c59cfd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M : RigidifiedLineBundle c ε t) (h : ∀ i, FibrewiseAlgEquivZero (M.pullbackAlong (f i))) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ σ

  obtain ⟨i, hi⟩ := hf (σ.base (IsLocalRing.closedPoint k))
  have hrange : Set.range σ.base ⊆ Set.range (f i).1.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    exact hi
  let σ' : Spec (CommRingCat.of k) ⟶ U i := IsOpenImmersion.lift (f i).1 σ hrange
  have hσ' : σ' ≫ (f i).1 = σ := IsOpenImmersion.lift_fac _ _ _

  set ψ : SchemeHomOver (u i) t := f i with hψ
  have w : (pullback.fst (pullback.snd c t) σ ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) σ ≫ σ') ≫ u i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← ψ.2, reassoc_of% hσ']
  let a : pullback (pullback.snd c t) σ ⟶ pullback c (u i) := pullback.lift _ _ w
  let e' : pullback (pullback.snd c t) σ ⟶ pullback (pullback.snd c (u i)) σ' :=
    pullback.lift a (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have he' : e' ≫ fibreAt c (u i) σ' = fibreAt c t σ := by
    simp only [e', fibreAt, pullback.lift_snd]
  have ha : a ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    apply pullback.hom_ext
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hσ']
      exact pullback.condition.symm
  have hcomp : (e' ≫ pullback.fst (pullback.snd c (u i)) σ') ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) σ := by
    rw [show e' ≫ pullback.fst _ _ = a from pullback.lift_fst _ _ _, ha]
  refine IsAlgEquivZero.of_iso ?_ ((h i k σ').pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L
end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
