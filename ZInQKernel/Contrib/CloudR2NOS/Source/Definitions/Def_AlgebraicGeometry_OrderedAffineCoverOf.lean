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
  Source file    : Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean
  Source sha256  : 04948efa319c03dffc263f12975cfffa13bd57853da0e865590ea545992d31b6
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

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
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

open CategoryTheory Opposite
r2nos_open_dual "CategoryTheory Opposite"

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

structure Scheme.OrderedAffineCoverOf {V : Scheme.{u}} (W : V.Opens) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  le : ∀ i, U i ≤ W
  iSup_eq : ⨆ i, U i = W

attribute [instance] Scheme.OrderedAffineCoverOf.instFintype Scheme.OrderedAffineCoverOf.instLinearOrder

namespace Scheme.OrderedAffineCoverOf
r2nos_namespace_dual

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _
instance (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j

theorem inter_le_base {i : ℕ} (s : K.Idx i) : K.inter s ≤ W := (iInf_le _ 0).trans (K.le _)

end Scheme.OrderedAffineCoverOf

namespace Scheme.OrderedAffineCover
r2nos_namespace_dual

def toCoverOf (K : V.OrderedAffineCover) : V.OrderedAffineCoverOf ⊤ where
  ι := K.ι
  U := K.U
  isAffineOpen := K.isAffineOpen
  le _ := le_top
  iSup_eq := K.iSup_eq_top

@[simp] theorem toCoverOf_U (K : V.OrderedAffineCover) (i : K.ι) : K.toCoverOf.U i = K.U i := rfl

def restrict (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) : V.OrderedAffineCoverOf W where
  ι := K.ι
  U i := K.U i ⊓ W
  isAffineOpen i := isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) hW
  le _ := inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]

@[simp] theorem restrict_U (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover) {W : V.Opens}
    (hW : IsAffineOpen W) (i : K.ι) : (K.restrict π hW).U i = K.U i ⊓ W := rfl

end Scheme.OrderedAffineCover

namespace Scheme.OrderedAffineCoverOf
r2nos_namespace_dual

variable (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W)

@[reducible] def moduleSections : ∀ O : V.Opens, Module R Γ(V, O) :=
  fun O => (Scheme.TwoAffineOpenCover.algebraOfHom π O).toModule

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, Γ(V, K.inter s)

def res {O O' : V.Opens} (h : O ≤ O') :
    letI := moduleSections π
    (Γ(V, O') : Type u) →ₗ[R] (Γ(V, O) : Type u) :=
  (OModulePresheaf.unit π).res h

theorem res_apply {O O' : V.Opens} (h : O ≤ O') (x : Γ(V, O')) :
    res π h x = (V.presheaf.map (homOfLE h).op).hom x := rfl

def d (i : ℕ) :
    letI := moduleSections π
    K.cochain i →ₗ[R] K.cochain (i + 1) :=
  letI := moduleSections π
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((res π (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (f : K.cochain i) (s : K.Idx (i + 1)) :
    letI := moduleSections π
    K.d π i f s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, res_apply]

def aug :
    letI := moduleSections π
    (Γ(V, W) : Type u) →ₗ[R] K.cochain 0 :=
  letI := moduleSections π
  LinearMap.pi fun s => res π (K.inter_le_base s)

theorem aug_apply (w : Γ(V, W)) (s : K.Idx 0) :
    letI := moduleSections π
    K.aug π w s = (V.presheaf.map (homOfLE (K.inter_le_base s)).op).hom w := rfl

abbrev H0 : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π 0)

abbrev HSucc (i : ℕ) : Type u :=
  letI := moduleSections π
  LinearMap.ker (K.d π (i + 1)) ⧸ (LinearMap.range (K.d π i)).comap (LinearMap.ker (K.d π (i + 1))).subtype

end Scheme.OrderedAffineCoverOf

theorem Scheme.OrderedAffineCover.d_toCoverOf (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover) (i : ℕ) :
    K.toCoverOf.d π i = (OModulePresheaf.unit π).d K i := rfl

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
