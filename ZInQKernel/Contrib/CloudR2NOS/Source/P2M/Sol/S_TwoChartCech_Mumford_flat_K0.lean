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
  Source file    : P2M/Sol/S_TwoChartCech_Mumford_flat_K0.lean
  Source sha256  : cd1ca335f50b442fae2828a9b680e08cefa89f3b124c471c58f3eece3e0c8248
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Prod
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_TwoChartCech_Mumford_flat_K0
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

universe u v w

namespace TwoChartCech
r2nos_namespace_dual
w03_export "TwoChartCech" "Mumford.K0"
namespace Mumford
r2nos_namespace_dual
w03_export "TwoChartCech.Mumford" "rank lift surjective_coprod K0"
w03_open "TwoChartCech.Mumford TwoChartCech"

variable {R : Type u} [CommRing R]

theorem flat_prod' {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have hN : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))
      = ((Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N)) ∘ₗ
          (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'
    intro a mn
    simp [TensorProduct.prodRight_tmul]
  intro x y hxy
  have hL : ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) x
      = ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) y := by
    simp only [LinearMap.comp_apply, hxy]
  rw [key] at hL
  simp only [LinearMap.comp_apply] at hL
  exact (TensorProduct.prodRight R R Q M N).injective ((hM.prodMap hN) hL)

theorem flat_ker_of_surjective' {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro Q' Q _ _ _ _ i hi
  have hι_Q' : Function.Injective ((LinearMap.ker f).subtype.lTensor Q') :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).subtype_injective
      (LinearMap.exact_subtype_ker_map f) Q'
  have hi_M : Function.Injective (i.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  intro x y hxy
  apply hι_Q'
  apply hi_M
  calc (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') x)
      = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    _ = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) y) := by rw [hxy]
    _ = (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') y) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end TwoChartCech.Mumford

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_flat_K0.TwoChartCech.Mumford in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_flat_K0.TwoChartCech.Mumford" in
theorem solution
    {R : Type u} [CommRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Flat R (TwoChartCech.Mumford.K0 d) :=
  haveI : Module.Flat R (C0 × (Fin (rank d) → R)) := flat_prod'
  flat_ker_of_surjective' (d.coprod (lift d)) (surjective_coprod d)

end
end S_TwoChartCech_Mumford_flat_K0
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
