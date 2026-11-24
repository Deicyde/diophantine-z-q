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
  Source file    : Definitions/Def_AlgebraicGeometry_IdealSheafHom.lean
  Source sha256  : de48031a8ba8dae8ecffe02865836c12404fcd8e5f881429cc602698fef3451e
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory TopologicalSpace Opposite
r2nos_open_dual "CategoryTheory TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry.Scheme
r2nos_namespace_dual

variable {X : Scheme.{u}}

namespace IdealSheafData
r2nos_namespace_dual

def sres {U V : X.affineOpens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom

def sresTop (U : X.affineOpens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom

lemma sres_apply {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, U)) :
    sres h s = (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom s := rfl

lemma sresTop_apply (U : X.affineOpens) (s : Γ(X, ⊤)) :
    sresTop U s = (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom s := rfl

@[simp] lemma sres_sresTop {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, ⊤)) :
    sres h (sresTop U s) = sresTop V s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl

@[simp] lemma sres_sres {U V W : X.affineOpens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    sres h (sres h' s) = sres (h.trans h') s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl

def resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U) :
    I.ideal V :=
  ⟨sres h (x : Γ(X, U)), I.ideal_le_comap_ideal h x.2⟩

@[simp] lemma coe_resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U)
    (x : I.ideal U) : (I.resLE h x : Γ(X, V)) = sres h (x : Γ(X, U)) := rfl

structure IdealHom (I J : X.IdealSheafData) : Type u where

  app : ∀ U : X.affineOpens, I.ideal U →ₗ[Γ(X, U)] J.ideal U

  coe_app_resLE : ∀ {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U),
    ((app V (I.resLE h x) : J.ideal V) : Γ(X, V)) = sres h ((app U x : J.ideal U) : Γ(X, U))

namespace IdealHom
r2nos_namespace_dual

variable {I J K : X.IdealSheafData}

@[ext]
lemma ext {φ ψ : IdealHom I J} (h : φ.app = ψ.app) : φ = ψ := by
  cases φ; cases ψ; congr

instance : Zero (IdealHom I J) := ⟨⟨fun _ => 0, fun h x => by simp⟩⟩
instance : Add (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U + ψ.app U, fun h x => by
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : Neg (IdealHom I J) :=
  ⟨fun φ => ⟨fun U => -φ.app U, fun h x => by
    simp only [LinearMap.neg_apply, Submodule.coe_neg, map_neg, φ.coe_app_resLE h x]⟩⟩
instance : Sub (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U - ψ.app U, fun h x => by
    simp only [LinearMap.sub_apply, Submodule.coe_sub, map_sub, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : SMul ℕ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_nsmul,
      φ.coe_app_resLE h x]⟩⟩
instance : SMul ℤ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_zsmul,
      φ.coe_app_resLE h x]⟩⟩

@[simp] lemma zero_app (U : X.affineOpens) : (0 : IdealHom I J).app U = 0 := rfl
@[simp] lemma add_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ + ψ).app U = φ.app U + ψ.app U := rfl
@[simp] lemma neg_app (φ : IdealHom I J) (U : X.affineOpens) : (-φ).app U = -φ.app U := rfl
@[simp] lemma sub_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ - ψ).app U = φ.app U - ψ.app U := rfl
@[simp] lemma nsmul_app (n : ℕ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl
@[simp] lemma zsmul_app (n : ℤ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl

instance : AddCommGroup (IdealHom I J) :=
  Function.Injective.addCommGroup (fun φ : IdealHom I J => φ.app)
    (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : SMul Γ(X, ⊤) (IdealHom I J) :=
  ⟨fun s φ => ⟨fun U => sresTop U s • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, SetLike.val_smul, smul_eq_mul, map_mul,
      φ.coe_app_resLE h x, sres_sresTop]⟩⟩

@[simp] lemma smul_app (s : Γ(X, ⊤)) (φ : IdealHom I J) (U : X.affineOpens) :
    (s • φ).app U = sresTop U s • φ.app U := rfl

instance : Module Γ(X, ⊤) (IdealHom I J) where
  one_smul φ := by ext U x; simp
  mul_smul r s φ := by ext U x; simp [mul_smul]
  smul_zero r := by ext U x; simp
  smul_add r φ ψ := by ext U x; simp
  add_smul r s φ := by ext U x; simp [add_smul]
  zero_smul φ := by ext U x; simp

def ofLE (h : I ≤ J) : IdealHom I J where
  app U := Submodule.inclusion (le_def.mp h U)
  coe_app_resLE _ _ := rfl

@[simp] lemma coe_ofLE_app (h : I ≤ J) (U : X.affineOpens) (x : I.ideal U) :
    ((ofLE h).app U x : Γ(X, U)) = x := rfl

protected def id (I : X.IdealSheafData) : IdealHom I I := ofLE le_rfl

@[simp] lemma id_app (I : X.IdealSheafData) (U : X.affineOpens) (x : I.ideal U) :
    (IdealHom.id I).app U x = x := rfl

def comp (ψ : IdealHom J K) (φ : IdealHom I J) : IdealHom I K where
  app U := ψ.app U ∘ₗ φ.app U
  coe_app_resLE := by
    intro U V h x
    have h₁ : φ.app V (I.resLE h x) = J.resLE h (φ.app U x) := Subtype.ext (φ.coe_app_resLE h x)
    simp only [LinearMap.coe_comp, Function.comp_apply, h₁, ψ.coe_app_resLE h]

@[simp] lemma comp_app (ψ : IdealHom J K) (φ : IdealHom I J) (U : X.affineOpens)
    (x : I.ideal U) : (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

def mulRight (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) : IdealHom I (I * J) where
  app U :=
    { toFun := fun x => ⟨x * sresTop U s, by rw [ideal_mul]; exact Ideal.mul_mem_mul x.2 (hs U)⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (mul_assoc _ _ _) }
  coe_app_resLE := by
    intro U V h x
    show sres h (x : Γ(X, U)) * sresTop V s = sres h ((x : Γ(X, U)) * sresTop U s)
    rw [map_mul, sres_sresTop]

@[simp] lemma coe_mulRight_app (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) (U : X.affineOpens) (x : I.ideal U) :
    ((mulRight I J s hs).app U x : Γ(X, U)) = x * sresTop U s :=
  rfl

def range (φ : IdealHom I J) : X.IdealSheafData where
  ideal U := LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U)
  map_ideal_basicOpen U f := by
    have hle : X.affineBasicOpen f ≤ U := X.affineBasicOpen_le f
    have hres : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = sres hle := rfl
    rw [hres]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      rintro _ ⟨x, rfl⟩
      exact ⟨I.resLE hle x, (φ.coe_app_resLE hle x)⟩
    · rintro _ ⟨y, rfl⟩

      let M : Submodule (Γ(X, X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) :=
        Submodule.comap ((J.ideal _).subtype ∘ₗ φ.app _)
          (Ideal.map (sres hle) (LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U)))
      suffices h : y ∈ M by rw [Submodule.mem_comap] at h; exact h
      have hle' : (I.ideal U).map (sres hle) ≤ M.map (I.ideal _).subtype := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        refine ⟨I.resLE hle ⟨x, hx⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply,
          φ.coe_app_resLE]
        exact Ideal.mem_map_of_mem (sres hle)
          (LinearMap.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩ : ((φ.app U ⟨x, hx⟩ : J.ideal U) : Γ(X, U)) ∈
            LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U))
      have hy : (y : Γ(X, X.affineBasicOpen f)) ∈ (I.ideal U).map (sres hle) :=
        (I.map_ideal_basicOpen U f).ge y.2
      obtain ⟨y', hy', hyy'⟩ := hle' hy
      have : y' = y := Subtype.ext hyy'
      exact this ▸ hy'

@[simp] lemma ideal_range (φ : IdealHom I J) (U : X.affineOpens) :
    φ.range.ideal U = LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U) := rfl

lemma range_le (φ : IdealHom I J) : φ.range ≤ J := fun U => by
  rintro _ ⟨x, rfl⟩; exact (φ.app U x).2

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme

end ZInQ.Contrib.CloudW03NeronSurj.FLT
