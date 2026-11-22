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
  Source file    : Definitions/Def_AlgebraicGeometry_OModulePresheafIdealFiltration.lean
  Source sha256  : 293f288aac752536366bf05735f7ebe37612b5ed57faca5f117c30bfb60fdd49
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.Algebra.Module.Submodule.RestrictScalars
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

namespace AlgebraicGeometry.OModulePresheaf
r2nos_namespace_dual

open CategoryTheory Opposite TopologicalSpace
r2nos_open_dual "CategoryTheory Opposite TopologicalSpace"

section IdealSmulInfra

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

def IdealAnnihilates (I : V.IdealSheafData) (F : OModulePresheaf π) : Prop :=
  ∀ U : V.affineOpens, ∀ a ∈ I.ideal U, ∀ x : F.obj U.1, a • x = 0

def idealSections (I : V.IdealSheafData) (U : V.Opens) : Ideal Γ(V, U) :=
  RingHom.ker (I.subschemeι.app U).hom

theorem idealSections_eq_ideal (I : V.IdealSheafData) (U : V.affineOpens) :
    idealSections I U.1 = I.ideal U :=
  I.ker_subschemeι_app U

theorem idealSections_res (I : V.IdealSheafData) {U U' : V.Opens} (h : U ≤ U')
    (a : Γ(V, U')) (ha : a ∈ idealSections I U') :
    (V.presheaf.map (homOfLE h).op).hom a ∈ idealSections I U := by
  show (I.subschemeι.app U).hom ((V.presheaf.map (homOfLE h).op).hom a) = 0
  rw [← CommRingCat.comp_apply, I.subschemeι.naturality, CommRingCat.comp_apply,
    show (I.subschemeι.app U').hom a = 0 from ha, map_zero]

theorem idealSections_pow_res (I : V.IdealSheafData) (k : ℕ)
    {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U'))
    (ha : a ∈ idealSections I U' ^ k) :
    (V.presheaf.map (homOfLE h).op).hom a ∈ idealSections I U ^ k := by
  have hle : (idealSections I U').map (V.presheaf.map (homOfLE h).op).hom
      ≤ idealSections I U :=
    Ideal.map_le_iff_le_comap.mpr fun b hb => idealSections_res I h b hb
  have hmap : ∀ m, (idealSections I U' ^ m).map (V.presheaf.map (homOfLE h).op).hom
      ≤ idealSections I U ^ m := by
    intro m
    rw [Ideal.map_pow]
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hle
  exact hmap k (Ideal.mem_map_of_mem _ ha)

def idealPowSub (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) : Submodule R (F.obj U) :=
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  (idealSections I U ^ k • (⊤ : Submodule Γ(V, U) (F.obj U))).restrictScalars R

theorem idealPowSub_res (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    {U U' : V.Opens} (h : U ≤ U') (x : F.obj U')
    (hx : x ∈ idealPowSub π I F k U') :
    F.res h x ∈ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U').toModule; haveI := F.isScalarTower U'
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSub, Submodule.restrictScalars_mem] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    rw [F.res_smul h a y]
    exact Submodule.smul_mem_smul (idealSections_pow_res I k h a ha) trivial
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz

def idealPow (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf π where
  obj U := idealPowSub π I F k U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U :=
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    inferInstanceAs (Module Γ(V, U)
      ((idealSections I U ^ k • (⊤ : Submodule _ _)).restrictScalars R))
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    exact inferInstanceAs (IsScalarTower R Γ(V, U)
      ((idealSections I U ^ k • (⊤ : Submodule _ _)).restrictScalars R))
  res {U U'} h := LinearMap.codRestrict (idealPowSub π I F k U)
    ((F.res h).comp (idealPowSub π I F k U').subtype)
    (fun x => idealPowSub_res π I F k h x.1 x.2)
  res_smul {U U'} h a x := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U').toModule; haveI := F.isScalarTower U'
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    exact Subtype.ext (F.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (F.res_refl U) x.1)
  res_comp {U U' U''} h h' := LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (F.res_comp h h') x.1)

theorem mem_idealPowSub_iff_of_affine (I : V.IdealSheafData) (F : OModulePresheaf π)
    (k : ℕ) (U : V.affineOpens) (x : F.obj U.1) :
    (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule R (F.obj U.1))).1 ∈
        idealPowSub π I F k U.1
      ↔ x ∈ (I.ideal U ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  rw [idealPowSub, Submodule.restrictScalars_mem,
    idealSections_eq_ideal]

end IdealSmulInfra

section QuotPMod

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem idealPowSub_antitone (I : V.IdealSheafData) (F : OModulePresheaf π)
    {k k' : ℕ} (h : k ≤ k') (U : V.Opens) :
    idealPowSub π I F k' U ≤ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  exact fun x hx => Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl hx

def idealPowSuccSub (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (U : V.Opens) :
    Submodule R ((idealPow π I F k).obj U) :=
  (idealPowSub π I F (k + 1) U).comap
    (idealPowSub π I F k U).subtype

theorem idealPowSub_smul_mem (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (x : F.obj U)
    (hx : x ∈ idealPowSub π I F k U) :
    a • x ∈ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSub, Submodule.restrictScalars_mem] at hx ⊢
  exact Submodule.smul_mem _ a hx

theorem idealPowSuccSub_smul_mem (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (x : (idealPow π I F k).obj U)
    (hx : x ∈ idealPowSuccSub π I F k U) :
    a • x ∈ idealPowSuccSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSuccSub, Submodule.mem_comap, idealPowSub,
    Submodule.restrictScalars_mem] at hx ⊢
  exact Submodule.smul_mem _ a hx

@[reducible]
def idealPowQuotModuleSections (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (U : V.Opens) :
    Module Γ(V, U) ((idealPow π I F k).obj U
      ⧸ idealPowSuccSub π I F k U) := by
  set p := idealPowSuccSub π I F k U
  letI : SMul Γ(V, U) (_ ⧸ p) :=
    { smul := fun a => Quotient.map' (a • ·) fun x y h => by
        rw [Submodule.quotientRel_def] at h ⊢
        rw [← smul_sub]; exact idealPowSuccSub_smul_mem π I F k U a (x - y) h }
  have key : ∀ (a : Γ(V, U)) (y : (idealPow π I F k).obj U),
      a • p.mkQ y = p.mkQ (a • y) := fun _ _ => rfl
  exact
  { smul := (· • ·)
    one_smul := fun x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, one_smul]
    mul_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, mul_smul]
    smul_zero := fun a => by rw [← map_zero p.mkQ, key, smul_zero]
    smul_add := fun a x₁ x₂ => by
      obtain ⟨y₁, rfl⟩ := p.mkQ_surjective x₁; obtain ⟨y₂, rfl⟩ := p.mkQ_surjective x₂
      rw [← map_add, key, smul_add, map_add, key, key]
    add_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, ← map_add, add_smul]
    zero_smul := fun x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, zero_smul, map_zero] }

theorem idealPowQuot_smul_mk (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (y : (idealPow π I F k).obj U) :
    letI := idealPowQuotModuleSections π I F k U
    a • (idealPowSuccSub π I F k U).mkQ y
      = (idealPowSuccSub π I F k U).mkQ (a • y) :=
  rfl

def idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf π where
  obj U := (idealPow π I F k).obj U ⧸ idealPowSuccSub π I F k U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := idealPowQuotModuleSections π I F k U
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; letI := idealPowQuotModuleSections π I F k U
    refine ⟨fun r a x => ?_⟩
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U).mkQ_surjective x
    rw [idealPowQuot_smul_mk, idealPowQuot_smul_mk, ← map_smul]
    exact congrArg _
      ((idealPow π I F k).isScalarTower U |>.smul_assoc r a y)
  res {U U'} h := Submodule.mapQ _ _ ((idealPow π I F k).res h)
    (fun x hx => idealPowSub_res π I F (k + 1) h _ hx)
  res_smul {U U'} h a x := by
    letI := idealPowQuotModuleSections π I F k U'
    letI := idealPowQuotModuleSections π I F k U
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U').mkQ_surjective x
    rw [idealPowQuot_smul_mk]
    show (idealPowSuccSub π I F k U).mkQ
        ((idealPow π I F k).res h (a • y)) = _
    rw [(idealPow π I F k).res_smul h a y, ← idealPowQuot_smul_mk]
    rfl
  res_refl U := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U).mkQ_surjective x
    exact congrArg ((idealPowSuccSub π I F k U).mkQ)
      (LinearMap.congr_fun ((idealPow π I F k).res_refl U) y)
  res_comp {U U' U''} h h' := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U'').mkQ_surjective x
    exact congrArg ((idealPowSuccSub π I F k U).mkQ)
      (LinearMap.congr_fun ((idealPow π I F k).res_comp h h') y)

def idealPowSuccInc (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf.AffHom (idealPow π I F (k + 1))
      (idealPow π I F k) where
  app U := Submodule.inclusion
    (idealPowSub_antitone π I F k.le_succ U.1)
  app_smul U a x := rfl
  naturality {U U'} h := LinearMap.ext fun x => Subtype.ext rfl

def idealPowSES (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf.AffSES (idealPow π I F (k + 1))
      (idealPow π I F k) (idealPowQuot π I F k) where
  inc := idealPowSuccInc π I F k
  proj :=
    { app := fun U => (idealPowSuccSub π I F k U.1).mkQ
      app_smul := fun U a y => (idealPowQuot_smul_mk π I F k U.1 a y).symm
      naturality := fun {U U'} h => LinearMap.ext fun _ => rfl }
  injective U := Submodule.inclusion_injective
    (idealPowSub_antitone π I F k.le_succ U.1)
  surjective U := (idealPowSuccSub π I F k U.1).mkQ_surjective
  exact U := by
    refine le_antisymm (LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun y => ?_)) fun x hx => ?_
    · show (idealPowSuccSub π I F k U.1).mkQ (Submodule.inclusion
        (idealPowSub_antitone π I F k.le_succ U.1) y) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr y.2
    · have hx' : x ∈ idealPowSuccSub π I F k U.1 :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx :
          (idealPowSuccSub π I F k U.1).mkQ x = 0)
      refine ⟨⟨(idealPowSub π I F k U.1).subtype x, hx'⟩, ?_⟩
      show Submodule.inclusion (idealPowSub_antitone π I F k.le_succ U.1) _ = x
      apply Subtype.ext
      show (idealPowSub π I F k U.1).subtype x
        = (idealPowSub π I F k U.1).subtype x
      rfl

theorem idealAnnihilates_idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    IdealAnnihilates π I (idealPowQuot π I F k) := by
  intro U a ha x
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  obtain ⟨y, rfl⟩ := (idealPowSES π I F k).surjective U x
  rw [← (idealPowSES π I F k).proj.app_smul U a y]
  show (idealPowSuccSub π I F k U.1).mkQ (a • y) = 0
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (show a • y ∈ idealPowSuccSub π I F k U.1 from ?_)
  show a • (idealPowSub π I F k U.1).subtype y
    ∈ idealPowSub π I F (k + 1) U.1
  rw [idealPowSub, Submodule.restrictScalars_mem, pow_succ',
    Submodule.mul_smul]
  exact Submodule.smul_mem_smul ((idealSections_eq_ideal I U).symm ▸ ha) y.2

end QuotPMod

section ZeroSES

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem idealPowSub_zero (I : V.IdealSheafData) (F : OModulePresheaf π)
    (U : V.Opens) : idealPowSub π I F 0 U = ⊤ := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  simp [idealPowSub, pow_zero, Submodule.top_smul]

def idealPowZeroSES (I : V.IdealSheafData) (F : OModulePresheaf π) :
    OModulePresheaf.AffSES (OModulePresheaf.zero π) (idealPow π I F 0) F where
  inc := OModulePresheaf.AffHom.zeroFrom _
  proj :=
    { app := fun U => (idealPowSub π I F 0 U.1).subtype
      app_smul := fun _ _ _ => rfl
      naturality := fun {U U'} h => LinearMap.ext fun x => rfl }
  injective _ _ _ _ := Subsingleton.elim _ _
  surjective U x := ⟨⟨x, idealPowSub_zero π I F U.1 ▸ Submodule.mem_top⟩, rfl⟩
  exact U := le_antisymm (fun _ ⟨_, hz⟩ => hz ▸ LinearMap.mem_ker.mpr rfl)
    (fun x hx => ⟨0, Subtype.ext (LinearMap.mem_ker.mp hx).symm⟩)

end ZeroSES

end AlgebraicGeometry.OModulePresheaf

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
