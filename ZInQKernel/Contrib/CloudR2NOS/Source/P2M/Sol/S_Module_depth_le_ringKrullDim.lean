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
  Source file    : P2M/Sol/S_Module_depth_le_ringKrullDim.lean
  Source sha256  : 3d136ace91408b2eee52f52c9312942a3a33e1b8cc0c290619724e91f0a283c0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_Patching_SystemTypes
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Module_depth_le_ringKrullDim
r2nos_namespace_dual

set_option autoImplicit false

open IsLocalRing RingTheory
r2nos_open_dual "IsLocalRing RingTheory"

namespace Module
r2nos_namespace_dual
w03_export "Module" "support mem_annihilator annihilator mk annihilator_eq_top_iff support_eq_empty_iff support_eq_zeroLocus length depth"
w03_open "Module"

variable (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

private lemma depth_le_krullDim_support' [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ Order.krullDim (Module.support R M) := by
  have : Nonempty (Module.support R M) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty,
      ne_eq, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
  cases h : Order.krullDim (Module.support R M) with
  | bot => simpa using Order.krullDim_nonneg.trans_eq h
  | coe n =>
  cases n with
  | top => simp
  | coe n =>
  clear this
  simp only [WithBot.coe_le_coe, ge_iff_le]
  induction n using Nat.strong_induction_on generalizing M with
  | h n IH =>
    rw [depth, sSup_le_iff]
    rintro _ ⟨l, hl, hl', rfl⟩
    apply WithTop.coe_le_coe.mpr ?_
    cases l with
    | nil => simp
    | cons x l =>
    simp only [Sequence.isWeaklyRegular_cons_iff] at hl
    have : Nontrivial (QuotSMulTop x M) := by
      apply Submodule.Quotient.nontrivial_iff.2
      rw [← Submodule.ideal_span_singleton_smul, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hl' _ (by simp)
    rw [Module.support_eq_zeroLocus, ← ringKrullDim_quotient] at h
    let f : (R ⧸ annihilator R M) ⧸ Ideal.span {(Ideal.Quotient.mk (annihilator R M)) x} →+*
        R ⧸ annihilator R (QuotSMulTop x M) :=
      Ideal.Quotient.lift _ (Ideal.quotientMap _ (.id R)
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
        (show Ideal.span _ ≤ RingHom.ker _ by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          simp only [SetLike.mem_coe, RingHom.mem_ker, Ideal.quotientMap_mk, RingHom.id_apply,
            Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
          intro m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact ⟨m, trivial, rfl⟩)
    have hf : Function.Surjective f := by
      apply Ideal.Quotient.lift_surjective_of_surjective
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective
    have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := R ⧸ annihilator R M)
        (r := Ideal.Quotient.mk _ x) (by
      rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        Module.mem_annihilator] at hz ⊢
      intro m
      apply hl.1
      simpa [smul_comm x, mul_smul] using hz m)
    rw [h] at this
    replace this := (add_le_add (ringKrullDim_le_of_surjective f hf) le_rfl).trans this
    cases h2 : ringKrullDim (R ⧸ annihilator R (QuotSMulTop x M)) with
    | bot =>
      have : Nontrivial (R ⧸ annihilator R (QuotSMulTop x M)) := by
        rw [Ideal.Quotient.nontrivial_iff, ← Submodule.annihilator_top, ne_eq,
          Submodule.annihilator_eq_top_iff]
        exact top_ne_bot
      have := ringKrullDim_nonneg_of_nontrivial.trans_eq h2
      simp at this
    | coe m =>
    cases m with
    | top =>
      have : (⊤ : ℕ∞) ≤ (n : ℕ) := by apply WithBot.coe_le_coe.mp; (simp only [h2] at this; exact this)
      cases (ENat.coe_lt_top n).not_ge this
    | coe m =>
    rw [h2] at this
    replace this : m + 1 ≤ n := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    replace IH := IH m (Nat.lt_of_succ_le this) (QuotSMulTop x M)
      (by rwa [Module.support_eq_zeroLocus, ← ringKrullDim_quotient])
    have hlen : (l.length : ℕ∞) ≤ (m : ℕ∞) := by
      have hld : l.length ≤ Module.depth R (QuotSMulTop x M) :=
        le_sSup ⟨l, hl.2, fun r hr => hl' r (List.mem_cons_of_mem _ hr), rfl⟩
      exact hld.trans IH
    replace hlen := WithTop.coe_le_coe.mp hlen
    simp only [List.length_cons, ge_iff_le]
    omega

private lemma depth_le_dim_annihilator' [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ Module.annihilator R M) := by
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact depth_le_krullDim_support' R M

end Module

theorem solution {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R :=
  (Module.depth_le_dim_annihilator' R M).trans (ringKrullDim_quotient_le _)
end S_Module_depth_le_ringKrullDim
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
