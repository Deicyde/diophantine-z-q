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
  Source file    : P2M/Sol/S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.lean
  Source sha256  : b7d0bd87beded778de3747d590f165315b385e11e2b050e488c32cb788a1d65d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u v w

noncomputable section

w03_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal LSpace ell mem_riemannRochSpace_iff"
namespace PlaceTransportGlue
r2nos_namespace_dual
w03_open "AlgebraicCurve"

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']


abbrev vsMap (σ : F ≃ₐ[K] F') (A : ValuationSubring F) : ValuationSubring F' :=
  A.comap (σ.symm : F' ≃ₐ[K] F).toAlgHom.toRingHom

theorem mem_vsMap_iff (σ : F ≃ₐ[K] F') (A : ValuationSubring F) (y : F') :
    y ∈ vsMap σ A ↔ σ.symm y ∈ A := Iff.rfl


def vsEquiv (σ : F ≃ₐ[K] F') (A : ValuationSubring F) : A ≃+* vsMap σ A where
  toFun x := ⟨σ x, by rw [mem_vsMap_iff, AlgEquiv.symm_apply_apply]; exact x.2⟩
  invFun y := ⟨σ.symm y, y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_vsEquiv_apply (σ : F ≃ₐ[K] F') (A : ValuationSubring F) (x : A) :
    ((vsEquiv σ A x : vsMap σ A) : F') = σ x := rfl


def placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : Place K F' where
  toValuationSubring := vsMap σ v.toValuationSubring
  algebraMap_mem' a := by
    rw [mem_vsMap_iff, AlgEquiv.commutes]
    exact v.algebraMap_mem' a
  ne_top' h := v.ne_top' <| by
    refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
    have hx : σ x ∈ vsMap σ v.toValuationSubring := h ▸ ValuationSubring.mem_top (σ x)
    rwa [mem_vsMap_iff, AlgEquiv.symm_apply_apply] at hx
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (vsEquiv σ v.toValuationSubring : _ ≃+* _)
      (vsEquiv σ v.toValuationSubring).surjective

@[scoped simp] theorem placeMap_toValuationSubring (σ : F ≃ₐ[K] F') (v : Place K F) :
    (placeMap σ v).toValuationSubring = vsMap σ v.toValuationSubring := rfl

theorem mem_placeMap_iff (σ : F ≃ₐ[K] F') (v : Place K F) (y : F') :
    y ∈ (placeMap σ v).toValuationSubring ↔ σ.symm y ∈ v.toValuationSubring := Iff.rfl

theorem placeMap_symm_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : placeMap σ.symm (placeMap σ v) = v := by
  ext x
  rw [mem_placeMap_iff, mem_placeMap_iff, AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]


def placeEquiv (σ : F ≃ₐ[K] F') : Place K F ≃ Place K F' where
  toFun := placeMap σ
  invFun := placeMap σ.symm
  left_inv v := placeMap_symm_placeMap σ v
  right_inv w := by simpa using placeMap_symm_placeMap σ.symm w

@[scoped simp] theorem placeEquiv_apply (σ : F ≃ₐ[K] F') (v : Place K F) : placeEquiv σ v = placeMap σ v := rfl
@[scoped simp] theorem placeEquiv_symm_apply (σ : F ≃ₐ[K] F') (w : Place K F') :
    (placeEquiv σ).symm w = placeMap σ.symm w := rfl

theorem coe_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) :
    ((placeMap σ v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F) := by
  ext y
  simp only [SetLike.mem_coe, mem_placeMap_iff, Set.mem_image]
  constructor
  · intro hy; exact ⟨σ.symm y, hy, σ.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩; rwa [AlgEquiv.symm_apply_apply]


theorem ord_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) (f : F) : (placeMap σ v).ord (σ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  let e : v.toValuationSubring ≃+* (placeMap σ v).toValuationSubring := vsEquiv σ v.toValuationSubring
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (placeMap σ v).toValuationSubring) : F') = σ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (placeMap σ v).toValuationSubring) : F') = σ (π : F) := rfl
  have key : σ f = ((hu'.unit : (placeMap σ v).toValuationSubring) : F')
      * (((e π : (placeMap σ v).toValuationSubring) : F') ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (placeMap σ v).ord_unit_smul_zpow hu'.unit hπ' n]


def residueAlgEquiv (σ : F ≃ₐ[K] F') (v : Place K F) : v.ResidueField ≃ₐ[K] (placeMap σ v).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv (vsEquiv σ v.toValuationSubring)) <| fun a => by
    have h3 : (vsEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (placeMap σ v).toValuationSubring a := by
      ext
      rw [coe_vsEquiv_apply, Place.coe_algebraMap, AlgEquiv.commutes]
      rfl
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

theorem deg_placeMap (σ : F ≃ₐ[K] F') (v : Place K F) : (placeMap σ v).deg = v.deg :=
  ((residueAlgEquiv σ v).toLinearEquiv.finrank_eq).symm

theorem mapDomain_placeEquiv_apply (σ : F ≃ₐ[K] F') (D : Divisor K F) (w : Place K F') :
    (Finsupp.mapDomain (placeEquiv σ) D) w = D ((placeEquiv σ).symm w) :=
  Finsupp.mapDomain_equiv_apply (f := placeEquiv σ) D w


def lSpaceEquiv (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    LSpace D ≃ₗ[K] LSpace (Finsupp.mapDomain (placeEquiv σ) D) where
  toFun f := ⟨σ f, by
    rw [mem_riemannRochSpace_iff]
    intro w
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · left; rw [h0, map_zero]
    right
    have hf := (mem_riemannRochSpace_iff.mp f.2) ((placeEquiv σ).symm w)
    rw [mapDomain_placeEquiv_apply]
    have hw : w = placeMap σ ((placeEquiv σ).symm w) := by
      rw [← placeEquiv_apply, Equiv.apply_symm_apply]
    rw [hw, ord_placeMap, ← hw]
    exact hf.resolve_left h0⟩
  invFun g := ⟨σ.symm g, by
    rw [mem_riemannRochSpace_iff]
    intro v
    rcases eq_or_ne (g : F') 0 with h0 | h0
    · left; rw [h0, map_zero]
    right
    have hg := (mem_riemannRochSpace_iff.mp g.2) (placeEquiv σ v)
    rw [mapDomain_placeEquiv_apply, Equiv.symm_apply_apply] at hg
    have h1 : (placeEquiv σ v).ord (g : F') = v.ord (σ.symm g) := by
      conv_lhs => rw [← σ.apply_symm_apply (g : F')]
      exact ord_placeMap σ v _
    rw [← h1]
    exact hg.resolve_left h0⟩
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem ell_mapDomain (σ : F ≃ₐ[K] F') (D : Divisor K F) : ell (Finsupp.mapDomain (placeEquiv σ) D) = ell D :=
  ((lSpaceEquiv σ D).finrank_eq).symm

theorem degree_mapDomain (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain (placeEquiv σ) D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single, Divisor.degree_single,
        Divisor.degree_single, placeEquiv_apply, deg_placeMap]

theorem isPrincipal_mapDomain_iff (σ : F ≃ₐ[K] F') (D : Divisor K F) :
    Divisor.IsPrincipal (Finsupp.mapDomain (placeEquiv σ) D) ↔ Divisor.IsPrincipal D := by
  constructor
  · rintro ⟨g, hg, hD⟩
    refine ⟨σ.symm g, by simpa using hg, fun v => ?_⟩
    have h := hD (placeEquiv σ v)
    rw [mapDomain_placeEquiv_apply, Equiv.symm_apply_apply] at h
    rw [h, placeEquiv_apply]
    conv_lhs => rw [← σ.apply_symm_apply g]
    exact ord_placeMap σ v _
  · rintro ⟨f, hf, hD⟩
    refine ⟨σ f, by simpa using hf, fun w => ?_⟩
    rw [mapDomain_placeEquiv_apply, hD]
    have hw : w = placeMap σ ((placeEquiv σ).symm w) := by
      rw [← placeEquiv_apply, Equiv.apply_symm_apply]
    conv_rhs => rw [hw]
    exact (ord_placeMap σ _ f).symm

end AlgebraicCurve.PlaceTransportGlue
w03_reactivate "P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve.PlaceTransportGlue"
w03_reactivate "P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve"

open AlgebraicCurve.PlaceTransportGlue in
r2nos_open_dual "AlgebraicCurve.PlaceTransportGlue" in

theorem solution
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (σ : F ≃ₐ[K] F') :
    ∃ π : Place K F ≃ Place K F',
      (∀ v : Place K F, ((π v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F)) ∧
      (∀ (v : Place K F) (f : F), (π v).ord (σ f) = v.ord f) ∧
      (∀ v : Place K F, (π v).deg = v.deg) ∧
      (∀ D : Divisor K F, ell (Finsupp.mapDomain π D) = ell D) ∧
      (∀ D : Divisor K F, Divisor.degree (Finsupp.mapDomain π D) = Divisor.degree D) ∧
      (∀ D : Divisor K F, Divisor.IsPrincipal (Finsupp.mapDomain π D) ↔ Divisor.IsPrincipal D) :=
  ⟨placeEquiv σ, coe_placeMap σ, ord_placeMap σ, deg_placeMap σ, ell_mapDomain σ, degree_mapDomain σ,
    isPrincipal_mapDomain_iff σ⟩

end
w03_reactivate "P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.AlgebraicCurve.PlaceTransportGlue"
end S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
