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
  Source file    : P2M/Sol/S_Module_Flat_of_flat_of_faithfullyFlat_right.lean
  Source sha256  : 2876a6d9af2be46fa7d76475da3a8e0324e89b107a995bf18768df2c21495b89
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Module_Flat_of_flat_of_faithfullyFlat_right
r2nos_namespace_dual

set_option autoImplicit false

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace Module
r2nos_namespace_dual
w03_export "Module" "Flat Flat.iff_lTensor_preserves_injective_linearMap Injective FaithfullyFlat FaithfullyFlat.lTensor_injective_iff_injective Flat.lTensor_preserves_injective_linearMap"
namespace Flat
r2nos_namespace_dual
w03_export "Module.Flat" "iff_lTensor_preserves_injective_linearMap baseChange lTensor_preserves_injective_linearMap"
end Module.Flat
r2nos_open_scoped "Module Module.Flat" in

theorem Module.Flat.of_flat_of_faithfullyFlat_right_aux (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  have key : ∀ x, TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
      (((f.baseChange S).lTensor T) x) =
      f.lTensor T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul t y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul s n => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
  have hT : Function.Injective (f.lTensor T) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  have : Function.Injective (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
      ((f.baseChange S).lTensor T)) := by
    rw [show (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
        ((f.baseChange S).lTensor T) : _ → _) =
        f.lTensor T ∘ TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N from funext key]
    exact hT.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).injective
  exact this.of_comp

theorem solution (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S :=
  Module.Flat.of_flat_of_faithfullyFlat_right_aux R S T
end S_Module_Flat_of_flat_of_faithfullyFlat_right
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
