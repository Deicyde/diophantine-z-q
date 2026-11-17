/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean
  Source sha256  : 973537bfc987bfc182fe0f7306c6ec549c4c6f34febe9902e2e030671cccf9fc
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct
r2nos_open_dual "CategoryTheory MonoidalCategory Opposite TensorProduct"

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

def tensorSectionsHom : L.val ⊗ M.val ⟶
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj (L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (tensorIsoSheafify L M).hom

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))

lemma tensorSections_def (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s t = DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
      ((tensorSectionsHom L M).app (op U)).hom
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))) := rfl

lemma tensorSections_add_left (s s' : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (s + s') t = tensorSections s t + tensorSections s' t := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.add_tmul, map_add]
  rfl

lemma tensorSections_add_right (s : Γ(L, U)) (t t' : Γ(M, U)) :
    tensorSections s (t + t') = tensorSections s t + tensorSections s t' := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.tmul_add, map_add]
  rfl

lemma tensorSections_smul_left (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (g • s) t = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [← TensorProduct.smul_tmul', LinearMap.map_smul]
  rfl

lemma tensorSections_smul_right (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (g • t) = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [TensorProduct.tmul_smul, LinearMap.map_smul]
  rfl

@[simp] lemma tensorSections_zero_left (t : Γ(M, U)) : tensorSections (0 : Γ(L, U)) t = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.zero_tmul, map_zero]

@[simp] lemma tensorSections_zero_right (s : Γ(L, U)) : tensorSections s (0 : Γ(M, U)) = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.tmul_zero, map_zero]

lemma tensorSections_neg_left (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (-s) t = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_left, neg_add_cancel, tensorSections_zero_left]

lemma tensorSections_neg_right (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (-t) = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_right, neg_add_cancel, tensorSections_zero_right]

lemma tensorSections_sum_left {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (∑ i ∈ S, s i) t = ∑ i ∈ S, tensorSections (s i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_left, ih]

lemma tensorSections_sum_right {ι : Type*} (S : Finset ι) (s : Γ(L, U)) (t : ι → Γ(M, U)) :
    tensorSections s (∑ i ∈ S, t i) = ∑ i ∈ S, tensorSections s (t i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_right, ih]

variable (L M U) in

def tensorSectionsBilin : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  LinearMap.mk₂ Γ(X, U) tensorSections tensorSections_add_left tensorSections_smul_left
    tensorSections_add_right tensorSections_smul_right

@[simp] lemma tensorSectionsBilin_apply (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSectionsBilin L M U s t = tensorSections s t := rfl

lemma map_tensorSections {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map i.op (tensorSections s t) =
      tensorSections (L.presheaf.map i.op s) (M.presheaf.map i.op t) := by
  rw [tensorSections_def, tensorSections_def]
  have h := PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
  exact h.symm

lemma map_homOfLE_tensorSections {V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map (homOfLE h).op (tensorSections s t) =
      tensorSections (L.presheaf.map (homOfLE h).op s) (M.presheaf.map (homOfLE h).op t) :=
  map_tensorSections (homOfLE h) s t

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

variable (U) in

def unitSection : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))

lemma unitSection_def : (unitSection U : Γ(𝟙_ X.Modules, U)) = (1 : Γ(X, U)) := rfl

@[simp] lemma map_unitSection {V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (unitSection U) = unitSection V :=
  (X.presheaf.map i.op).hom.map_one

lemma smul_unitSection (g : Γ(X, U)) : g • unitSection U = (g : Γ(X, U)) :=
  mul_one g

lemma smul_unitSection_bijective : Function.Bijective fun g : Γ(X, U) => g • unitSection U := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun x => (x : Γ(X, U)), fun g => ?_, fun x => ?_⟩
  · exact mul_one g
  · exact mul_one (show Γ(X, U) from x)

def tensorPowSection (s : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSection U
  | n + 1 => tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s

@[simp] lemma tensorPowSection_zero (s : Γ(L, U)) : tensorPowSection s 0 = unitSection U := rfl

lemma tensorPowSection_succ (s : Γ(L, U)) (n : ℕ) :
    tensorPowSection s (n + 1) = tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s := rfl

lemma tensorPowSection_one (s : Γ(L, U)) :
    tensorPowSection s 1 = tensorSections (L := 𝟙_ X.Modules) (M := L) (unitSection U) s := rfl

lemma map_tensorPowSection {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (n : ℕ) :
    (L.tensorPow n).presheaf.map i.op (tensorPowSection s n) =
      tensorPowSection (L.presheaf.map i.op s) n := by
  induction n with
  | zero => exact map_unitSection i
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ← ih]
    exact map_tensorSections (L := L.tensorPow n) (M := L) i _ s

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

def IsFrameOn (s : Γ(M, U)) (V : X.Opens) : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))

namespace IsFrameOn
r2nos_namespace_dual

variable {s : Γ(M, U)} {V : X.Opens}

lemma bijective (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W)) :=
  h hWU hWV

lemma mono (h : IsFrameOn s V) {V' : X.Opens} (hV' : V' ≤ V) : IsFrameOn s V' :=
  fun _ hWU hWV' => h hWU (hWV'.trans hV')

lemma of_inf (h : IsFrameOn s (V ⊓ U)) : IsFrameOn s V :=
  fun _ hWU hWV => h hWU (le_inf hWV hWU)

lemma inf_iff : IsFrameOn s (V ⊓ U) ↔ IsFrameOn s V :=
  ⟨of_inf, fun h => h.mono inf_le_left⟩

lemma map (h : IsFrameOn s V) {U' : X.Opens} (i : U' ⟶ U) :
    IsFrameOn (M.presheaf.map i.op s) V := by
  intro W hWU' hWV
  have e : M.presheaf.map (homOfLE hWU').op (M.presheaf.map i.op s) =
      M.presheaf.map (homOfLE (hWU'.trans i.le)).op s := by
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  simp only [e]
  exact h (hWU'.trans i.le) hWV

lemma existsUnique (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(M, W)) :
    ∃! g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op s = x :=
  (Function.bijective_iff_existsUnique _).1 (h hWU hWV) x

lemma smul_eq_zero_iff (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) :
    g • M.presheaf.map (homOfLE hWU).op s = 0 ↔ g = 0 := by
  constructor
  · intro hg
    apply (h hWU hWV).1
    change g • M.presheaf.map (homOfLE hWU).op s = (0 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s
    rw [hg, zero_smul]
  · rintro rfl
    exact zero_smul _ _

end IsFrameOn

lemma isFrameOn_unitSection (V : X.Opens) : IsFrameOn (unitSection U) V := by
  intro W hWU _
  have e : (𝟙_ X.Modules).presheaf.map (homOfLE hWU).op (unitSection U) = unitSection W :=
    map_unitSection _
  simp only [e]
  exact smul_unitSection_bijective

lemma IsFrameOn.map_iso {N : X.Modules} {s : Γ(M, U)} {V : X.Opens} (h : IsFrameOn s V) (e : M ≅ N) :
    IsFrameOn (e.hom.app U s) V := by
  intro W hWU hWV
  have nat : N.presheaf.map (homOfLE hWU).op (e.hom.app U s) =
      e.hom.app W (M.presheaf.map (homOfLE hWU).op s) := by
    have := (e.hom.mapPresheaf).naturality (homOfLE hWU).op
    exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, W))) this) s).symm
  simp only [nat]
  have hb : Function.Bijective (e.hom.app W : Γ(M, W) → Γ(N, W)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app W, fun x => ?_, fun y => ?_⟩
    · change (e.hom.app W ≫ e.inv.app W) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    · change (e.inv.app W ≫ e.hom.app W) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
  have : (fun g : Γ(X, W) => g • e.hom.app W (M.presheaf.map (homOfLE hWU).op s)) =
      (e.hom.app W) ∘ fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul]
  rw [this]
  exact hb.comp (h hWU hWV)

end Frame

end AlgebraicGeometry.Scheme.Modules

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
