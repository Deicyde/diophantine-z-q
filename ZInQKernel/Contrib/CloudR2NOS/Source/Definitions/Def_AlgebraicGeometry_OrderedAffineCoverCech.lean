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
  Source file    : Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean
  Source sha256  : 16080c5da453c9fd5f0389f079bc60ff58b9b73f42fe627dcdff75b966f4709d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Pi
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

open CategoryTheory Opposite TopologicalSpace
r2nos_open_dual "CategoryTheory Opposite TopologicalSpace"

structure Scheme.OrderedAffineCover (V : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤

attribute [instance] Scheme.OrderedAffineCover.instFintype Scheme.OrderedAffineCover.instLinearOrder

namespace Scheme.OrderedAffineCover
r2nos_namespace_dual

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance instFintypeIdx (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _

instance instDecidableEqIdx (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem face_val {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : (K.face s j).1 = s.1 ∘ Fin.succAbove j :=
  rfl

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

variable (V) in

def ofAffine [IsAffine V] : V.OrderedAffineCover where
  ι := PUnit.{u + 1}
  U _ := ⊤
  isAffineOpen _ := isAffineOpen_top V
  iSup_eq_top := iSup_const

theorem ofAffine_U [IsAffine V] (i : PUnit.{u + 1}) : (ofAffine V).U i = ⊤ := rfl

end Scheme.OrderedAffineCover

namespace Scheme.TwoAffineOpenCover
r2nos_namespace_dual

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)

def toOrderedAffineCover : X.OrderedAffineCover where
  ι := ULift.{u} (Fin 2)
  instLinearOrder := LinearOrder.lift' ULift.down ULift.down_injective
  U i := ![𝒱.U0, 𝒱.U1] i.down
  isAffineOpen i := by
    rcases i with ⟨i⟩
    fin_cases i
    · exact 𝒱.isAffineOpen_U0
    · exact 𝒱.isAffineOpen_U1
  iSup_eq_top := by
    rw [eq_top_iff, ← 𝒱.sup_eq_top]
    exact sup_le (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨0⟩)
      (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨1⟩)

theorem toOrderedAffineCover_ι : 𝒱.toOrderedAffineCover.ι = ULift.{u} (Fin 2) := rfl
theorem toOrderedAffineCover_U_zero : 𝒱.toOrderedAffineCover.U ⟨0⟩ = 𝒱.U0 := rfl
theorem toOrderedAffineCover_U_one : 𝒱.toOrderedAffineCover.U ⟨1⟩ = 𝒱.U1 := rfl
theorem toOrderedAffineCover_U (i : ULift.{u} (Fin 2)) : 𝒱.toOrderedAffineCover.U i = ![𝒱.U0, 𝒱.U1] i.down := rfl

end Scheme.TwoAffineOpenCover

structure OModulePresheaf {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) where

  obj : V.Opens → Type u
  [addCommGroup : ∀ U, AddCommGroup (obj U)]

  [module : ∀ U, Module R (obj U)]

  [moduleSections : ∀ U, Module Γ(V, U) (obj U)]

  [isScalarTower : ∀ U, letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    IsScalarTower R Γ(V, U) (obj U)]

  res : ∀ {U U' : V.Opens}, U ≤ U' → obj U' →ₗ[R] obj U

  res_smul : ∀ {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : obj U'),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x

  res_refl : ∀ U, res (le_refl U) = LinearMap.id

  res_comp : ∀ {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U''), res (h.trans h') = res h ∘ₗ res h'

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module OModulePresheaf.moduleSections
  OModulePresheaf.isScalarTower

namespace OModulePresheaf
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem res_refl_apply (U : V.Opens) (x : F.obj U) : F.res (le_refl U) x = x := by
  rw [F.res_refl]; rfl

theorem res_res {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U'') (x : F.obj U'') :
    F.res h (F.res h' x) = F.res (h.trans h') x := by
  rw [F.res_comp h h']; rfl

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, F.obj (K.inter s)

def d (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) :
    F.d K i c s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.inter_le_inter_face s j) (c (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

abbrev H0 : Submodule R (F.cochain K 0) := LinearMap.ker (F.d K 0)

abbrev HSucc (i : ℕ) : Type u :=
  LinearMap.ker (F.d K (i + 1)) ⧸ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype

def CechFinite : Prop := Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i)

theorem cechFinite_iff : F.CechFinite K ↔ Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i) :=
  Iff.rfl

def IsCoherent : Prop := ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1)

theorem isCoherent_iff : F.IsCoherent ↔ ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1) := Iff.rfl

def IsQuasicoherent : Prop :=
  ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
    (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
        F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
      ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0)

theorem isQuasicoherent_iff : F.IsQuasicoherent ↔
    ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
      (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
          F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
        ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0) :=
  Iff.rfl

def SupportedIn (Y : Closeds V) : Prop :=
  ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U)

theorem supportedIn_iff (Y : Closeds V) :
    F.SupportedIn Y ↔ ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U) :=
  Iff.rfl

variable (π) in

def unit : OModulePresheaf π where
  obj U := Γ(V, U)
  addCommGroup _ := inferInstance
  module U := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule
  moduleSections _ := Semiring.toModule
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact IsScalarTower.right
  res {U U'} h :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
    (Scheme.TwoAffineOpenCover.restrictAlgHom π h).toLinearMap
  res_smul h a x := by
    show (V.presheaf.map (homOfLE h).op).hom (a * x)
      = (V.presheaf.map (homOfLE h).op).hom a * (V.presheaf.map (homOfLE h).op).hom x
    exact map_mul _ a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    refine LinearMap.ext fun x => ?_
    show (V.presheaf.map (homOfLE (le_refl U)).op).hom x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), V.presheaf.map_id]; rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U''
    refine LinearMap.ext fun x => ?_
    show (V.presheaf.map (homOfLE (h.trans h')).op).hom x
      = (V.presheaf.map (homOfLE h).op).hom ((V.presheaf.map (homOfLE h').op).hom x)
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem unit_obj (U : V.Opens) : (unit π).obj U = Γ(V, U) := rfl

theorem unit_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(V, U')) :
    (unit π).res h (show (unit π).obj U' from x) = (V.presheaf.map (homOfLE h).op).hom x :=
  rfl

theorem unit_smul (U : V.Opens) (a x : Γ(V, U)) :
    a • (show (unit π).obj U from x) = (show (unit π).obj U from a * x) := rfl

theorem unit_algebraMap_smul (U : V.Opens) (r : R) (x : Γ(V, U)) :
    r • (show (unit π).obj U from x)
      = (show (unit π).obj U from (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r * x) :=
  rfl

section TwoChart

variable (𝒱 : V.TwoAffineOpenCover)

def twoChartSections : TwoChartCech.Sections (𝒱.cover π) :=
  letI : Module (𝒱.cover π).A0 (F.obj 𝒱.U0) := inferInstanceAs (Module Γ(V, 𝒱.U0) (F.obj 𝒱.U0))
  letI : Module (𝒱.cover π).A1 (F.obj 𝒱.U1) := inferInstanceAs (Module Γ(V, 𝒱.U1) (F.obj 𝒱.U1))
  letI : Module (𝒱.cover π).A01 (F.obj (𝒱.U0 ⊓ 𝒱.U1)) :=
    inferInstanceAs (Module Γ(V, 𝒱.U0 ⊓ 𝒱.U1) (F.obj (𝒱.U0 ⊓ 𝒱.U1)))
  haveI : IsScalarTower R (𝒱.cover π).A0 (F.obj 𝒱.U0) := F.isScalarTower 𝒱.U0
  haveI : IsScalarTower R (𝒱.cover π).A1 (F.obj 𝒱.U1) := F.isScalarTower 𝒱.U1
  haveI : IsScalarTower R (𝒱.cover π).A01 (F.obj (𝒱.U0 ⊓ 𝒱.U1)) := F.isScalarTower (𝒱.U0 ⊓ 𝒱.U1)
  { M0 := F.obj 𝒱.U0
    M1 := F.obj 𝒱.U1
    M01 := F.obj (𝒱.U0 ⊓ 𝒱.U1)
    r0 := F.res inf_le_left
    r1 := F.res inf_le_right
    r0_smul := fun a m => F.res_smul inf_le_left a m
    r1_smul := fun a m => F.res_smul inf_le_right a m }

theorem twoChartSections_M0 : (F.twoChartSections 𝒱).M0 = F.obj 𝒱.U0 := rfl
theorem twoChartSections_M1 : (F.twoChartSections 𝒱).M1 = F.obj 𝒱.U1 := rfl
theorem twoChartSections_M01 : (F.twoChartSections 𝒱).M01 = F.obj (𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem twoChartSections_r0_apply (x : F.obj 𝒱.U0) :
    (F.twoChartSections 𝒱).r0 (show (F.twoChartSections 𝒱).M0 from x) = F.res inf_le_left x := rfl
theorem twoChartSections_r1_apply (x : F.obj 𝒱.U1) :
    (F.twoChartSections 𝒱).r1 (show (F.twoChartSections 𝒱).M1 from x) = F.res inf_le_right x := rfl

end TwoChart

end OModulePresheaf

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
