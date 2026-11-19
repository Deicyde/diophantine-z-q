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
  Source file    : Definitions/Def_HopfAlgebra_HopfKer.lean
  Source sha256  : 97ebc95aa2b649956109cf34f165825d0c4613522c8c88a365f13b914727121d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

namespace HopfAlgebra
r2nos_namespace_dual

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]

noncomputable def coaction (π : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)).comp (Bialgebra.comulAlgHom R A)

theorem coaction_apply (π : A →ₐc[R] B) (a : A) :
    coaction π a = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) (Coalgebra.comul (R := R) a) := rfl

noncomputable def hopfKer (π : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (coaction π) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)

theorem mem_hopfKer_iff (π : A →ₐc[R] B) (a : A) : a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 := Iff.rfl

theorem coaction_eq_of_mem (π : A →ₐc[R] B) {a : A} (h : a ∈ hopfKer π) : coaction π a = a ⊗ₜ[R] 1 := h

noncomputable def canAlgHom (π : A →ₐc[R] B) : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (coaction π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem canAlgHom_tmul (π : A →ₐc[R] B) (a a' : A) :
    canAlgHom π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  Algebra.TensorProduct.lift_tmul _ _ _ a a'

noncomputable def canMap (π : A →ₐc[R] B) : A ⊗[R] A →ₗ[R] A ⊗[R] B := (canAlgHom π).toLinearMap

theorem canMap_apply (π : A →ₐc[R] B) (z : A ⊗[R] A) : canMap π z = canAlgHom π z := rfl

@[simp] theorem canMap_tmul (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canAlgHom_tmul π a a'

theorem canMap_mul_tmul (π : A →ₐc[R] B) (a a' : A) {h : A} (hh : h ∈ hopfKer π) :
    canMap π ((a * h) ⊗ₜ[R] a') = canMap π (a ⊗ₜ[R] (h * a')) := by
  rw [canMap_tmul, canMap_tmul, map_mul, coaction_eq_of_mem π hh, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

theorem canMap_tmul_one (π : A →ₐc[R] B) (a : A) : canMap π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canMap_tmul, map_one, mul_one]

theorem canMap_one_tmul (π : A →ₐc[R] B) (a : A) : canMap π (1 ⊗ₜ[R] a) = coaction π a := by
  rw [canMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]

def balancingRelations (π : A →ₐc[R] B) : Set (A ⊗[R] A) :=
  {x | ∃ (a h a' : A), h ∈ hopfKer π ∧ x = (a * h) ⊗ₜ[R] a' - a ⊗ₜ[R] (h * a')}

theorem canMap_eq_zero_of_mem_span (π : A →ₐc[R] B) {z : A ⊗[R] A}
    (hz : z ∈ Submodule.span R (balancingRelations π)) : canMap π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, h, a', hh, rfl⟩ := hx
    rw [map_sub, canMap_mul_tmul π a a' hh, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

def IsHopfGalois (π : A →ₐc[R] B) : Prop :=
  Function.Surjective (canMap π) ∧ ∀ z, canMap π z = 0 → z ∈ Submodule.span R (balancingRelations π)

end HopfAlgebra

end ZInQ.Contrib.CloudW03NeronSurj.FLT
