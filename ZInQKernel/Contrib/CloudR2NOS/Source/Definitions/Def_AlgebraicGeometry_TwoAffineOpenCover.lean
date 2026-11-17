/-
NEW EDITION CANDIDATE 003 (H5 lane4 , 2026-11-17; supersedes candidate 002 of this module). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean
  Source sha256  : 15a726949c8adc67ab7693592f369dea36a1d08df4f8ebe8489f57e13ba9396e
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 generalized-field-notation use(s) `x.f` of a port-prefixed extension declaration on a ROOT-namespace type rewritten to explicit application `(T.f x)` (dot notation follows the receiver type's root head constant, which the prefix does not reach; lead 2026-11-17T07:27Z).
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
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

namespace AlgebraicGeometry
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits Opposite
r2nos_open_dual "CategoryTheory CategoryTheory.Limits Opposite"

structure Scheme.TwoAffineOpenCover (X : Scheme.{u}) where

  U0 : X.Opens

  U1 : X.Opens
  isAffineOpen_U0 : IsAffineOpen U0
  isAffineOpen_U1 : IsAffineOpen U1
  sup_eq_top : U0 ⊔ U1 = ⊤
  isAffineOpen_inf : IsAffineOpen (U0 ⊓ U1)

namespace Scheme.TwoAffineOpenCover
r2nos_namespace_dual

abbrev specMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[reducible] def algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) (r : R) :
    (algebraOfHom c U).algebraMap r = (c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) :=
  rfl

def restrictAlgHom (c : X ⟶ Spec (.of R)) {U V : X.Opens} (h : V ≤ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c V
    Γ(X, U) →ₐ[R] Γ(X, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => by
      change (c.appLE ⊤ U le_top ≫ X.presheaf.map (homOfLE h).op).hom _ = (c.appLE ⊤ V le_top).hom _
      rw [Scheme.Hom.appLE_map] }

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

def cover : TwoChartCech.Cover.{u, u} R :=
  letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1; letI := algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  { A0 := Γ(X, 𝒱.U0)
    A1 := Γ(X, 𝒱.U1)
    A01 := Γ(X, 𝒱.U0 ⊓ 𝒱.U1)
    ρ0 := restrictAlgHom c inf_le_left
    ρ1 := restrictAlgHom c inf_le_right }

theorem cover_A0 : (𝒱.cover c).A0 = Γ(X, 𝒱.U0) := rfl
theorem cover_A1 : (𝒱.cover c).A1 = Γ(X, 𝒱.U1) := rfl
theorem cover_A01 : (𝒱.cover c).A01 = Γ(X, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem cover_ρ0_apply (x : (𝒱.cover c).A0) :
    (𝒱.cover c).ρ0 x = (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom x := rfl
theorem cover_ρ1_apply (x : (𝒱.cover c).A1) :
    (𝒱.cover c).ρ1 x = (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom x := rfl

abbrev structureSheafSections : TwoChartCech.Sections (𝒱.cover c) := (𝒱.cover c).structureSheaf

abbrev lineBundleSections (t : (𝒱.cover c).A01ˣ) : TwoChartCech.Sections (𝒱.cover c) :=
  (𝒱.cover c).lineBundle t

omit [CommRing R] in
theorem res_res {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem restrict_mem_H0 (s : Γ(X, ⊤)) :
    ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
      (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
      ∈ (𝒱.structureSheafSections c).H0 := by
  refine (TwoChartCech.Sections.mem_H0_iff _ _).mpr ?_
  change (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s)
    = ((1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)ˣ) : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) •
      (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom
        ((X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
  rw [Units.val_one, one_smul, res_res, res_res]

def toH0 : letI := algebraOfHom c ⊤; Γ(X, ⊤) →ₗ[R] (𝒱.structureSheafSections c).H0 :=
  letI := algebraOfHom c ⊤; letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1
  LinearMap.codRestrict _
    (((restrictAlgHom c (le_top : 𝒱.U0 ≤ ⊤)).toLinearMap).prod
      ((restrictAlgHom c (le_top : 𝒱.U1 ≤ ⊤)).toLinearMap))
    (fun s => 𝒱.restrict_mem_H0 c s)

theorem toH0_apply_coe (s : Γ(X, ⊤)) :
    letI := algebraOfHom c ⊤
    ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) =
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
        (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s) := rfl

section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]

theorem isAffineHom_fst : IsAffineHom (Limits.pullback.fst c (specMap R A)) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

def pullback : (AlgebraicGeometry.Scheme.TwoAffineOpenCover (Limits.pullback c (specMap R A))) :=
  haveI := isAffineHom_fst c A
  { U0 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0
    U1 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

@[simp] theorem pullback_U0 : (𝒱.pullback c A).U0 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0 := rfl
@[simp] theorem pullback_U1 : (𝒱.pullback c A).U1 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1 := rfl

end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
