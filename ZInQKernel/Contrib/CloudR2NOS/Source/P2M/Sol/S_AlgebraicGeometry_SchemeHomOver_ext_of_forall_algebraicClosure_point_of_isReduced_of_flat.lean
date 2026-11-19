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
  Source file    : P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean
  Source sha256  : bfb625cdc43e117f9bd0ec483c3a1dd439b7d7775f390d60728b211866dc591d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R5×8; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra
r2nos_open_dual "CategoryTheory AlgebraicGeometry NeronModelInfra"

open Topology CategoryTheory.Limits
r2nos_open_dual "Topology CategoryTheory.Limits"

namespace RigKerGeomPoints
r2nos_namespace_dual

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L] [IsAlgClosed L] [Algebra R L]

local notation "bL" => Spec.map (CommRingCat.ofHom (algebraMap R L))

theorem range_specMap_eq (hinj : Function.Injective (algebraMap R L)) :
    Set.range (bL).base = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      haveI := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

omit [IsAlgClosed L] [Algebra R L] in

theorem dense_preimage_genericPoint {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ t.base p := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen
  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

theorem dense_range_of_points (hinj : Function.Injective (algebraMap R L))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = bL},
      Set.range x.1.base) := by
  let P := pullback t bL
  haveI : LocallyOfFiniteType (pullback.snd t bL) := inferInstance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t bL)
  have hsub : (pullback.fst t bL).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = bL}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    let y := (pointEquivClosedPoint (pullback.snd t bL)).symm ⟨p, hp⟩
    have hy : y.1 ≫ pullback.fst t bL ≫ t = bL := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t bL, by rw [Category.assoc]; exact hy⟩,
      ⟨IsLocalRing.closedPoint L, ?_⟩⟩
    change (pullback.fst t bL).base (y.1.base (IsLocalRing.closedPoint L)) = _
    congr 1
    have := pointEquivClosedPoint_symm_apply_coe (pullback.snd t bL) ⟨p, hp⟩
    change y.1 = _ at this
    rw [this, pointOfClosedPoint_apply]
  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  have hrange : Set.range (pullback.fst t bL).base = t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_specMap_eq hinj]
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t bL).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact (map_mem_closure (pullback.fst t bL).base.hom.continuous this fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

theorem ext_of_forall_geometric_point (hinj : Function.Injective (algebraMap R L))
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (CommRingCat.of R)) (s : X ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated s] [IsReduced Y]
    (φ ψ : Y ⟶ X) (hφ : φ ≫ s = t) (hψ : ψ ≫ s = t)
    (h : ∀ x : Spec (CommRingCat.of L) ⟶ Y, x ≫ t = bL → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of L) ⟶ Y // x ≫ t = bL}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of L)
  let ι : W ⟶ Y := Sigma.desc fun x : I => x.1
  haveI : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_of_points (L := L) hinj t
    refine Dense.mono ?_ hd
    intro d hd'
    obtain ⟨x, ⟨p, rfl⟩⟩ := Set.mem_iUnion.mp hd'
    refine ⟨(Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x).base p, ?_⟩
    change (Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x ≫ ι).base p = _
    rw [Sigma.ι_desc]
  refine ext_of_isDominant_of_isSeparated s (hφ.trans hψ.symm) ι ?_
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_desc]
  exact h x.1 x.2

end RigKerGeomPoints

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    [Flat gY] [LocallyOfFiniteType gY] [IsReduced Y] [IsSeparated gX]
    (φ ψ : SchemeHomOver gY gX)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gY, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  haveI : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K
  have hinj : Function.Injective (algebraMap R Kbar) := by
    rw [IsScalarTower.algebraMap_eq R K Kbar]
    exact (algebraMap K Kbar).injective.comp (IsFractionRing.injective R K)
  apply Subtype.ext
  exact RigKerGeomPoints.ext_of_forall_geometric_point (L := Kbar) hinj gY gX φ.1 ψ.1 φ.2 ψ.2
    (fun x hx => h ⟨x, hx⟩)
end S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
