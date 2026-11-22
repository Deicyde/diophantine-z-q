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
  Source file    : P2M/Sol/S_TwoChartCech_Mumford_bijective_cokerMapBaseChange.lean
  Source sha256  : 23b83c7d0b47c51337cdf81f0a50da9ea5fa394d77f8edbd4c84afa1c47c8cdb
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
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_TwoChartCech_Mumford_bijective_cokerMapBaseChange
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

universe u

namespace TwoChartCech
r2nos_namespace_dual
w03_export "TwoChartCech" "Mumford.dK Mumford.ι0 Mumford.ι1 Mumford.comm cokerMapBaseChange"
namespace Mumford
r2nos_namespace_dual
w03_export "TwoChartCech.Mumford" "rank lift surjective_coprod K0 dK ι0 ι1 ι1_eq comm"
w03_open "TwoChartCech.Mumford TwoChartCech"

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
variable (A : Type u) [CommRing A] [Algebra R A]

theorem mem_range_subtype_baseChange (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w = 0 ↔ ∃ z, ((K0 d).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 d).subtype.baseChange A) = ⇑((K0 d).subtype.lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  have heqc : ⇑((d.coprod (lift d)).baseChange A) = ⇑((d.coprod (lift d)).lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod d) w

theorem prodRight_apply_eq_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact rfl
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

theorem prodRight_subtype_baseChange (z : A ⊗[R] K0 d) :
    (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) (((K0 d).subtype.baseChange A) z)
      = (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · show ((LinearMap.fst R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · show ((LinearMap.snd R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl

theorem coprod_baseChange_apply (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w
      = (d.baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1
        + ((lift d).baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2 := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
  | tmul a x => simp [TensorProduct.prodRight_tmul, LinearMap.coprod_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]; abel

theorem cokerMapBaseChange_surjective :
    Function.Surjective (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    have hsurj : Function.Surjective ((d.coprod (lift d)).baseChange A) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective A (surjective_coprod d)
    obtain ⟨w, rfl⟩ := hsurj y
    refine ⟨Submodule.Quotient.mk (-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2), ?_⟩
    show Submodule.Quotient.mk (((ι1 d)).baseChange A _) = _
    rw [ι1_eq, LinearMap.baseChange_neg, LinearMap.neg_apply, map_neg, neg_neg, coprod_baseChange_apply,
      Submodule.Quotient.eq]
    refine ⟨-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1, ?_⟩
    rw [map_neg]; abel

theorem cokerMapBaseChange_injective :
    Function.Injective (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    have hq' : ((ι1 d).baseChange A) v ∈ LinearMap.range (d.baseChange A) := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact hq
    obtain ⟨x, hx⟩ := hq'
    rw [ι1_eq, LinearMap.baseChange_neg, LinearMap.neg_apply] at hx
    set w := (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).symm (x, v) with hwdef
    have hw : ((d.coprod (lift d)).baseChange A) w = 0 := by
      rw [coprod_baseChange_apply, hwdef, LinearEquiv.apply_symm_apply, hx, neg_add_cancel]
    obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w).mp hw
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨z, ?_⟩
    show ((dK d).baseChange A) z = v
    have := congrArg Prod.snd (prodRight_subtype_baseChange d A z)
    rw [hz, hwdef, LinearEquiv.apply_symm_apply] at this
    exact this.symm

end TwoChartCech.Mumford

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_bijective_cokerMapBaseChange.TwoChartCech.Mumford in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_bijective_cokerMapBaseChange.TwoChartCech.Mumford" in
theorem solution
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.cokerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) :=
  ⟨cokerMapBaseChange_injective d A, cokerMapBaseChange_surjective d A⟩

end
end S_TwoChartCech_Mumford_bijective_cokerMapBaseChange
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
