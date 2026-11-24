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
  Source file    : Definitions/Def_AlgebraicGeometry_FGSubalgebraTensorStage.lean
  Source sha256  : a6b91d103baa22713996b29265736db9945db0a73b32e39e7d0ace68e53dc8dd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace AlgebraicGeometry.FGSubalgebra
r2nos_namespace_dual

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (Γ : Type u) [CommRing Γ] [Algebra k Γ]

abbrev tensorStage (D : FGSubalgebra k A) : Type u := Γ ⊗[k] ↥D.1

noncomputable abbrev tensorStageMap (D D' : FGSubalgebra k A) (h : D ≤ D') :
    tensorStage k A Γ D →ₐ[Γ] tensorStage k A Γ D' :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) (Subalgebra.inclusion (show D.1 ≤ D'.1 from h))

noncomputable abbrev tensorStageToColimit (D : FGSubalgebra k A) : tensorStage k A Γ D →ₐ[Γ] Γ ⊗[k] A :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) D.1.val

instance tensorStage_directedSystem : DirectedSystem (tensorStage k A Γ) (fun i j h => tensorStageMap k A Γ i j h) where
  map_self := fun i x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_map := fun i j l hij hjl x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comp (i j : FGSubalgebra k A) (h : i ≤ j) :
    (tensorStageToColimit k A Γ j).comp (tensorStageMap k A Γ i j h) = tensorStageToColimit k A Γ i := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul γ d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comm (D : FGSubalgebra k A) (u : ↥D.1 ⊗[k] Γ) :
    tensorStageToColimit k A Γ D (TensorProduct.comm k _ _ u) = TensorProduct.comm k _ _ (D.1.val.toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageMap_comm (D D' : FGSubalgebra k A) (h : D ≤ D') (u : ↥D.1 ⊗[k] Γ) :
    tensorStageMap k A Γ D D' h (TensorProduct.comm k _ _ u) =
      TensorProduct.comm k _ _ ((Subalgebra.inclusion (show D.1 ≤ D'.1 from h)).toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_surj (b : Γ ⊗[k] A) : ∃ (D : FGSubalgebra k A) (x : tensorStage k A Γ D), tensorStageToColimit k A Γ D x = b := by
  obtain ⟨D, hD, u, hu⟩ := TensorProduct.Algebra.exists_of_fg (TensorProduct.comm k _ _ b)
  refine ⟨⟨D, hD⟩, TensorProduct.comm k _ _ u, ?_⟩
  rw [tensorStageToColimit_comm, hu, ← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply]

theorem tensorStageToColimit_zero (D : FGSubalgebra k A) (x : tensorStage k A Γ D) (hx : tensorStageToColimit k A Γ D x = 0) :
    ∃ (D' : FGSubalgebra k A) (h : D ≤ D'), tensorStageMap k A Γ D D' h x = 0 := by
  have hx' : D.1.val.toLinearMap.rTensor Γ ((TensorProduct.comm k _ _).symm x) =
      D.1.val.toLinearMap.rTensor Γ 0 := by
    rw [map_zero]
    have := tensorStageToColimit_comm k A Γ D ((TensorProduct.comm k _ _).symm x)
    rw [LinearEquiv.apply_symm_apply, hx] at this
    exact (LinearEquiv.map_eq_zero_iff _).mp this.symm
  obtain ⟨D', hDD', hD', h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq D.2 hx'
  refine ⟨⟨D', hD'⟩, hDD', ?_⟩
  rw [map_zero] at h
  have := tensorStageMap_comm k A Γ D ⟨D', hD'⟩ hDD' ((TensorProduct.comm k _ _).symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, h, map_zero]

end AlgebraicGeometry.FGSubalgebra

end ZInQ.Contrib.CloudW03NeronSurj.FLT
