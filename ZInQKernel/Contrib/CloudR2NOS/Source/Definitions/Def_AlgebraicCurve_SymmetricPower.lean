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
  Source file    : Definitions/Def_AlgebraicCurve_SymmetricPower.lean
  Source sha256  : 74a801805deab702fdaa8ea4c2f0cbb47109eeeaa4c36644cb261cbddd7282d2
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-2 HAND REPAIRS (lane4, recorded): Mathlib 56a0058 CategoryTheory/Endomorphism.lean l.123–125: `structure Aut (X) where of ::… (×1); Aut.ext then Iso.ext; `mul x y := .of (y.asIso.trans x.asIso)` (Endomorphism.lean l.146–14… (×1); `(permAct c r σ).hom` → `.asIso.hom` (Aut is a structure)… (×7)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
r2nos_open_dual "CategoryTheory CategoryTheory.Limits"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

noncomputable abbrev finFibrePow : Scheme.{u} :=
  widePullback (Spec (CommRingCat.of k)) (fun _ : Fin r => C) (fun _ => c)

namespace finFibrePow
r2nos_namespace_dual

noncomputable abbrev proj (l : Fin r) : finFibrePow c r ⟶ C :=
  WidePullback.π (fun _ : Fin r => c) l

noncomputable abbrev toBase : finFibrePow c r ⟶ Spec (CommRingCat.of k) :=
  WidePullback.base (fun _ : Fin r => c)

@[reassoc]
theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _

noncomputable def permHom (σ : Equiv.Perm (Fin r)) : finFibrePow c r ⟶ finFibrePow c r :=
  WidePullback.lift (toBase c r) (fun j => proj c r (σ⁻¹ j)) (fun _ => WidePullback.π_arrow _ _)

@[reassoc]
theorem permHom_proj (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    permHom c r σ ≫ proj c r j = proj c r (σ⁻¹ j) :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc]
theorem permHom_toBase (σ : Equiv.Perm (Fin r)) : permHom c r σ ≫ toBase c r = toBase c r :=
  WidePullback.lift_base _ _ _ _

theorem permHom_one : permHom c r 1 = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.id_comp, inv_one, Equiv.Perm.one_apply]
  · rw [permHom_toBase, Category.id_comp]

theorem permHom_mul (σ τ : Equiv.Perm (Fin r)) :
    permHom c r (σ * τ) = permHom c r τ ≫ permHom c r σ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.assoc, permHom_proj, permHom_proj, mul_inv_rev,
      Equiv.Perm.mul_apply]
  · rw [permHom_toBase, Category.assoc, permHom_toBase, permHom_toBase]

noncomputable def permAut (σ : Equiv.Perm (Fin r)) : Aut (finFibrePow c r) := Aut.of
  { hom := permHom c r σ
    inv := permHom c r σ⁻¹
    hom_inv_id := by rw [← permHom_mul, inv_mul_cancel, permHom_one]
    inv_hom_id := by rw [← permHom_mul, mul_inv_cancel, permHom_one] }

noncomputable def permAct : Equiv.Perm (Fin r) →* Aut (finFibrePow c r) :=
  MonoidHom.mk' (permAut c r) (fun σ τ => by
    ext : 2
    change permHom c r (σ * τ) = (permAut c r τ).asIso.hom ≫ (permAut c r σ).asIso.hom
    exact permHom_mul c r σ τ)

theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).asIso.hom = permHom c r σ := rfl

theorem permAct_inv (σ : Equiv.Perm (Fin r)) : (permAct c r σ).asIso.inv = permHom c r σ⁻¹ := rfl

@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).asIso.hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).asIso.hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow

theorem le_preimage_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ X) (q : X ⟶ Y) (h : g ≫ q = q)
    (V : Y.Opens) : q ⁻¹ᵁ V ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, h]

end AlgebraicGeometry

namespace AlgebraicCurve
r2nos_namespace_dual

open AlgebraicGeometry
r2nos_open_dual "AlgebraicGeometry"

structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where

  Csym : Scheme.{u}

  csym : Csym ⟶ Spec (CommRingCat.of k)

  π : finFibrePow c r ⟶ Csym

  π_comp_csym : π ≫ csym = finFibrePow.toBase c r

  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom ≫ π = π

  isFinite_π : IsFinite π

  surjective_π : Surjective π

  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔ ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom.base x = x'

  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)

  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}

  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U

  integral : IsIntegral Csym

  proper : IsProper csym

  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve

end ZInQ.Contrib.CloudW03NeronSurj.FLT
