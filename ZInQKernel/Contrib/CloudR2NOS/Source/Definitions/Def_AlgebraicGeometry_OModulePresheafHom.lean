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
  Source file    : Definitions/Def_AlgebraicGeometry_OModulePresheafHom.lean
  Source sha256  : d3d041eb66646a34fac9d8516284fc1d750a037a4b6eefdaff034d309b073e99
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Separated
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

open CategoryTheory Opposite Limits
r2nos_open_dual "CategoryTheory Opposite Limits"

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover
r2nos_namespace_dual

variable (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated [IsSeparated π] {U W : V.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter [IsSeparated π] {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → K.ι), IsAffineOpen (⨅ j, K.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, K.U (t j)) = K.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact K.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), K.U (t j)) = K.U (t 0) ⊓ (⨅ j : Fin (m + 1), K.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated π (K.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

abbrev affineInter [IsSeparated π] {i : ℕ} (s : K.Idx i) : V.affineOpens :=
  ⟨K.inter s, K.isAffineOpen_inter π s⟩

end Scheme.OrderedAffineCover

namespace OModulePresheaf
r2nos_namespace_dual

variable {π : V ⟶ Spec (.of R)}

structure Hom (F G : OModulePresheaf π) where

  app : ∀ U : V.Opens, F.obj U →ₗ[R] G.obj U
  app_smul : ∀ (U : V.Opens) (a : Γ(V, U)) (x : F.obj U), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.Opens} (h : U ≤ U'), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure SES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : Hom F₁ F₂

  proj : Hom F₂ F₃
  injective : ∀ U : V.Opens, Function.Injective (inc.app U)
  surjective : ∀ U : V.Opens, Function.Surjective (proj.app U)
  exact : ∀ U : V.Opens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

structure AffHom (F G : OModulePresheaf π) where

  app : ∀ U : V.affineOpens, F.obj U.1 →ₗ[R] G.obj U.1
  app_smul : ∀ (U : V.affineOpens) (a : Γ(V, U.1)) (x : F.obj U.1), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.affineOpens} (h : U.1 ≤ U'.1), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure AffSES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : AffHom F₁ F₂

  proj : AffHom F₂ F₃
  injective : ∀ U : V.affineOpens, Function.Injective (inc.app U)
  surjective : ∀ U : V.affineOpens, Function.Surjective (proj.app U)
  exact : ∀ U : V.affineOpens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

namespace Hom
r2nos_namespace_dual

variable {F G H : OModulePresheaf π}

def appSections (φ : Hom F G) (U : V.Opens) : F.obj U →ₗ[Γ(V, U)] G.obj U :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : Hom F G) {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in

protected def id : Hom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

def comp (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    show ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality, LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.Opens) (x : F.obj U) : (Hom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : Hom G H) (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

def toAffHom (φ : Hom F G) : AffHom F G where
  app U := φ.app U.1
  app_smul U := φ.app_smul U.1
  naturality h := φ.naturality h

@[simp] theorem toAffHom_app (φ : Hom F G) (U : V.affineOpens) : φ.toAffHom.app U = φ.app U.1 := rfl

end Hom

namespace AffHom
r2nos_namespace_dual

variable {F G H : OModulePresheaf π}

def appSections (φ : AffHom F G) (U : V.affineOpens) : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1 :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : AffHom F G) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F.obj U'.1) :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in

protected def id : AffHom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

def comp (ψ : AffHom G H) (φ : AffHom F G) : AffHom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    show ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality, LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.affineOpens) (x : F.obj U.1) : (AffHom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : AffHom G H) (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

end AffHom

def SES.toAffSES {F₁ F₂ F₃ : OModulePresheaf π} (S : SES F₁ F₂ F₃) : AffSES F₁ F₂ F₃ where
  inc := S.inc.toAffHom
  proj := S.proj.toAffHom
  injective U := S.injective U.1
  surjective U := S.surjective U.1
  exact U := S.exact U.1

section Cochains

variable [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}

def AffHom.cochainMap (φ : AffHom F G) (i : ℕ) : F.cochain K i →ₗ[R] G.cochain K i :=
  LinearMap.pi fun s => (φ.app (K.affineInter π s)).comp (LinearMap.proj s)

theorem AffHom.cochainMap_apply (φ : AffHom F G) (i : ℕ) (f : F.cochain K i) (s : K.Idx i) :
    φ.cochainMap K i f s = φ.app (K.affineInter π s) (f s) := rfl

theorem AffHom.cochainMap_comp_d (φ : AffHom F G) (i : ℕ) :
    φ.cochainMap K (i + 1) ∘ₗ F.d K i = G.d K i ∘ₗ φ.cochainMap K i := by
  refine LinearMap.ext fun f => funext fun s => ?_
  simp only [LinearMap.comp_apply, AffHom.cochainMap_apply, OModulePresheaf.d_apply, map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg _
    (φ.naturality_apply (U := K.affineInter π s) (U' := K.affineInter π (K.face s j))
      (K.inter_le_inter_face s j) _)

def AffHom.kerMap (φ : AffHom F G) (i : ℕ) :
    LinearMap.ker (F.d K i) →ₗ[R] LinearMap.ker (G.d K i) :=
  (φ.cochainMap K i).restrict fun f hf => LinearMap.mem_ker.mpr <| by
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hf, map_zero]

@[simp] theorem AffHom.kerMap_coe (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K i)) :
    (φ.kerMap K i x : G.cochain K i) = φ.cochainMap K i x := rfl

abbrev AffHom.H0Map (φ : AffHom F G) : F.H0 K →ₗ[R] G.H0 K := φ.kerMap K 0

def AffHom.HSuccMap (φ : AffHom F G) (i : ℕ) : F.HSucc K i →ₗ[R] G.HSucc K i :=
  Submodule.mapQ _ _ (φ.kerMap K (i + 1)) fun x hx => by
    obtain ⟨g, hg⟩ := (Submodule.mem_comap.mp hx)
    refine Submodule.mem_comap.mpr ⟨φ.cochainMap K i g, ?_⟩
    show G.d K i _ = φ.cochainMap K (i + 1) x.1
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg]
    rfl

theorem AffHom.HSuccMap_mk (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K (i + 1))) :
    φ.HSuccMap K i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.kerMap K (i + 1) x) := rfl

end Cochains

end OModulePresheaf

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
