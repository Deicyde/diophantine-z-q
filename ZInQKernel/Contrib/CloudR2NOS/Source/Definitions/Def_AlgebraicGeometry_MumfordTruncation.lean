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
  Source file    : Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean
  Source sha256  : 73b06c8acc272ea1b9a9b81177b95e243b13b6ab837fb93ac9194c187561e7f8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-2 HAND REPAIRS (lane4, recorded): universe of the unannotated `PUnit` now defaults to 1 (`Membership (R × PUnit.{u+1}) (Subm… (×1)
-/

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech
r2nos_namespace_dual

namespace KerCoprod
r2nos_namespace_dual

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

theorem mem_K0_iff (z : C0 × P) : z ∈ K0 d g ↔ d z.1 + g z.2 = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

def dK : K0 d g →ₗ[R] P := (LinearMap.snd R C0 P) ∘ₗ (K0 d g).subtype

def ι0 : K0 d g →ₗ[R] C0 := (LinearMap.fst R C0 P) ∘ₗ (K0 d g).subtype

def ι1 : P →ₗ[R] C1 := -g

@[simp] theorem dK_apply (z : K0 d g) : dK d g z = (z : C0 × P).2 := rfl
@[simp] theorem ι0_apply (z : K0 d g) : ι0 d g z = (z : C0 × P).1 := rfl
@[simp] theorem ι1_apply (p : P) : ι1 g p = -g p := rfl
theorem ι1_eq : ι1 g = -g := rfl

theorem comm : d ∘ₗ ι0 d g = ι1 g ∘ₗ dK d g := by
  ext z
  have hz : d (z : C0 × P).1 + g (z : C0 × P).2 = 0 := (mem_K0_iff d g _).mp z.2
  simp only [LinearMap.comp_apply, ι0_apply, dK_apply, ι1_apply, eq_neg_iff_add_eq_zero]
  exact hz

theorem ι0_prod_dK : (ι0 d g).prod (dK d g) = (K0 d g).subtype := by
  ext z <;> rfl

end KerCoprod

namespace Mumford
r2nos_namespace_dual

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

theorem mkQ_lift_apply (v : Fin (rank d) → R) : (LinearMap.range d).mkQ (lift d v) = quot d v := by
  rw [← LinearMap.comp_apply, mkQ_comp_lift]

theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv, mkQ_lift_apply, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := KerCoprod.K0 d (lift d)

theorem mem_K0_iff (z : C0 × (Fin (rank d) → R)) : z ∈ K0 d ↔ d z.1 + lift d z.2 = 0 :=
  KerCoprod.mem_K0_iff d (lift d) z

abbrev dK : K0 d →ₗ[R] (Fin (rank d) → R) := KerCoprod.dK d (lift d)

abbrev ι0 : K0 d →ₗ[R] C0 := KerCoprod.ι0 d (lift d)

abbrev ι1 : (Fin (rank d) → R) →ₗ[R] C1 := KerCoprod.ι1 (lift d)

@[simp] theorem dK_apply (z : K0 d) : dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
@[simp] theorem ι0_apply (z : K0 d) : ι0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl
@[simp] theorem ι1_apply (v : Fin (rank d) → R) : ι1 d v = -lift d v := rfl
theorem ι1_eq : ι1 d = -lift d := rfl

theorem comm : d ∘ₗ ι0 d = ι1 d ∘ₗ dK d := KerCoprod.comm d (lift d)

theorem ι0_prod_dK : (ι0 d).prod (dK d) = (K0 d).subtype := KerCoprod.ι0_prod_dK d (lift d)

end Mumford

section Gates

example (x : ℤ) (v : Fin (Mumford.rank (0 : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (x, v) ∈ Mumford.K0 (0 : ℤ →ₗ[ℤ] ℤ) ↔ Mumford.lift (0 : ℤ →ₗ[ℤ] ℤ) v = 0 := by
  rw [Mumford.mem_K0_iff, LinearMap.zero_apply, zero_add]

example (v : Fin (Mumford.rank (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (-(Mumford.lift (LinearMap.id : ℤ →ₗ[ℤ] ℤ) v), v) ∈ Mumford.K0 (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  rw [Mumford.mem_K0_iff, LinearMap.id_apply, neg_add_cancel]

example (R : Type u) [CommRing R] :
    (0 : R →ₗ[R] R) ∘ₗ Mumford.ι0 (0 : R →ₗ[R] R) = Mumford.ι1 (0 : R →ₗ[R] R) ∘ₗ Mumford.dK (0 : R →ₗ[R] R) :=
  Mumford.comm 0

example (R : Type u) [CommRing R] (d : R →ₗ[R] R) (x : R) (p : PUnit.{u + 1}) :
    (x, p) ∈ KerCoprod.K0 d (0 : PUnit.{u + 1} →ₗ[R] R) ↔ d x = 0 := by
  rw [KerCoprod.mem_K0_iff, LinearMap.zero_apply, add_zero]

end Gates

end TwoChartCech

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
