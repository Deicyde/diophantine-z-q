/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_PresheafOfModules_ExteriorPower.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
r2nos_open_dual "CategoryTheory"
namespace PresheafOfModules
r2nos_namespace_dual

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower
r2nos_namespace_dual

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

section map
variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

@[reducible] noncomputable def moduleAlong (R : Cᵒᵖ ⥤ CommRingCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (N : Type u) [AddCommGroup N] [Module (R.obj Y) N] : Module (R.obj X) N :=
  Module.compHom N (R.map f).hom

noncomputable def mapAlong :
    letI := moduleAlong R f (M.obj Y)
    M.obj X →ₗ[R.obj X] M.obj Y :=
  letI := moduleAlong R f (M.obj Y)
  { toFun := fun x => (M.map f x : M.obj Y)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => M.map_smul f r x }

noncomputable def ιMultiAlong :
    letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    (M.obj Y) [⋀^Fin n]→ₗ[R.obj X] (⋀[R.obj Y]^n (M.obj Y)) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (R.obj X) (R.obj Y) (⋀[R.obj Y]^n (M.obj Y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { (exteriorPower.ιMulti (R.obj Y) n).toMultilinearMap.restrictScalars (R.obj X) with
    map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti (R.obj Y) n).map_eq_zero_of_eq v h hij }

noncomputable def mapₗ :
    letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    ⋀[R.obj X]^n (M.obj X) →ₗ[R.obj X] ⋀[R.obj Y]^n (M.obj Y) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exteriorPower.alternatingMapLinearEquiv ((ιMultiAlong n M f).compLinearMap (mapAlong M f))

lemma mapₗ_ιMulti (m : Fin n → M.obj X) :
    mapₗ n M f (exteriorPower.ιMulti (R.obj X) n m) = exteriorPower.ιMulti (R.obj Y) n (M := M.obj Y) (fun i => M.map f (m i)) := by
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  simp [mapₗ]
  rfl

lemma mapₗ_smul (r : R.obj X) (x : ⋀[R.obj X]^n (M.obj X)) :
    mapₗ n M f (r • x) = R.map f r • mapₗ n M f x := by
  letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exact (mapₗ n M f).map_smul r x

end map

lemma addMonoidHom_ext {X : Cᵒᵖ} {N : Type*} [AddCommGroup N] {φ ψ : ⋀[R.obj X]^n (M.obj X) →+ N}
    (hsmul : ∀ (r : R.obj X) x, φ x = ψ x → φ (r • x) = ψ (r • x))
    (h : ∀ m : Fin n → M.obj X, φ (exteriorPower.ιMulti (R.obj X) n m) = ψ (exteriorPower.ιMulti (R.obj X) n m)) :
    φ = ψ := by
  ext x
  have hx : x ∈ Submodule.span (R.obj X) (Set.range (exteriorPower.ιMulti (R.obj X) n (M := M.obj X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h m
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => exact hsmul r x hx

noncomputable def presheafAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (⋀[R.obj X]^n (M.obj X))
  map {X Y} f := AddCommGrpCat.ofHom (letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y)); (mapₗ n M f).toAddMonoidHom)
  map_id X := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (𝟙 X) (r • x) = r • x
      rw [mapₗ_smul, R.map_id]; exact congrArg (r • ·) hx
    · change mapₗ n M (𝟙 X) _ = exteriorPower.ιMulti (R.obj X) n m
      rw [mapₗ_ιMulti]
      congr 1; funext i
      rw [M.map_id]
      rfl
  map_comp {X Y Z} f g := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (f ≫ g) (r • x) = mapₗ n M g (mapₗ n M f (r • x))
      rw [mapₗ_smul, mapₗ_smul, mapₗ_smul, R.map_comp]; exact congrArg (_ • ·) hx
    · change mapₗ n M (f ≫ g) _ = mapₗ n M g (mapₗ n M f _)
      rw [mapₗ_ιMulti, mapₗ_ιMulti, mapₗ_ιMulti]
      congr 1; funext i
      exact M.map_comp_apply f g (m i)

noncomputable instance instModulePresheafAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheafAb n M).obj X) :=
  inferInstanceAs (Module (R.obj X) (⋀[R.obj X]^n (M.obj X)))

end ExteriorPower

noncomputable def exteriorPower (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  @ofPresheaf C _ (R ⋙ forget₂ CommRingCat RingCat) (ExteriorPower.presheafAb n M)
    (fun X => ExteriorPower.instModulePresheafAb n M X)
    (fun _ _ f r x => by
      change ExteriorPower.mapₗ n M f (r • x) = R.map f r • ExteriorPower.mapₗ n M f x
      exact ExteriorPower.mapₗ_smul n M f r x)

@[simp] lemma exteriorPower_map_ιMulti (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : Fin n → M.obj X) :
    ((exteriorPower n M).map f (show (exteriorPower n M).obj X from exteriorPower.ιMulti (R.obj X) n m) :
        ⋀[R.obj Y]^n (M.obj Y)) = exteriorPower.ιMulti (R.obj Y) n (M := M.obj Y) (fun i => M.map f (m i)) :=
  ExteriorPower.mapₗ_ιMulti n M f m

end PresheafOfModules

namespace PresheafOfModules
r2nos_namespace_dual

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower
r2nos_namespace_dual

variable (n : ℕ) {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

noncomputable def appₗ (φ : M ⟶ N) (X : Cᵒᵖ) : M.obj X →ₗ[R.obj X] N.obj X where
  toFun x := φ.app X x
  map_add' x y := map_add (φ.app X).hom x y
  map_smul' r x := (φ.app X).hom.map_smul r x

@[simp] lemma appₗ_apply (φ : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) : appₗ φ X x = φ.app X x := rfl

lemma appₗ_id (X : Cᵒᵖ) : appₗ (𝟙 M) X = LinearMap.id := rfl

lemma appₗ_comp (φ : M ⟶ N) (ψ : N ⟶ P) (X : Cᵒᵖ) :
    appₗ (φ ≫ ψ) X = appₗ ψ X ∘ₗ appₗ φ X := rfl

noncomputable def mapAb (φ : M ⟶ N) : presheafAb n M ⟶ presheafAb n N where
  app X := AddCommGrpCat.ofHom (exteriorPower.map n (appₗ φ X)).toAddMonoidHom
  naturality {X Y} f := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f x) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) x) at hx
      change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (r • x)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (r • x))
      rw [mapₗ_smul, map_smul, map_smul, mapₗ_smul]
      exact congrArg (R.map f r • ·) hx
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (exteriorPower.ιMulti _ n m)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (exteriorPower.ιMulti _ n m))
      rw [mapₗ_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, mapₗ_ιMulti]
      congr 1
      funext i
      exact naturality_apply φ f (m i)

end ExteriorPower

noncomputable def exteriorPowerMap (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) : exteriorPower n M ⟶ exteriorPower n N :=
  homMk (ExteriorPower.mapAb n φ) (fun X r m =>
    (exteriorPower.map n (ExteriorPower.appₗ φ X)).map_smul (show R.obj X from r) m)

lemma exteriorPowerMap_app_apply (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (x : ⋀[R.obj X]^n (M.obj X)) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from x) : ⋀[R.obj X]^n (N.obj X)) =
      exteriorPower.map n (ExteriorPower.appₗ φ X) x := rfl

lemma exteriorPowerMap_app_ιMulti (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (m : Fin n → M.obj X) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from exteriorPower.ιMulti (R.obj X) n m) :
      ⋀[R.obj X]^n (N.obj X)) = exteriorPower.ιMulti (R.obj X) n (fun i => φ.app X (m i)) :=
  exteriorPower.map_apply_ιMulti _ _

variable (R) in

noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := exteriorPower n M
  map φ := exteriorPowerMap n φ
  map_id M := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (𝟙 M) X) x = x
    rw [ExteriorPower.appₗ_id, exteriorPower.map_id]
    rfl
  map_comp φ ψ := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (φ ≫ ψ) X) x =
      exteriorPower.map n (ExteriorPower.appₗ ψ X) (exteriorPower.map n (ExteriorPower.appₗ φ X) x)
    rw [ExteriorPower.appₗ_comp, exteriorPower.map_comp]
    rfl

end PresheafOfModules


end ZInQ.Contrib.CloudW03NeronSurj.FLT
