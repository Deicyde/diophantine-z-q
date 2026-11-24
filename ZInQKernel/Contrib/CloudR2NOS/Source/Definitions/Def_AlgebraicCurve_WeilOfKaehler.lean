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
  Source file    : Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean
  Source sha256  : 7ff2144c83df5f312adfc880f915f09cb69712dda8af9d15550302ce2cbb59a4
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero Module IsLocalRing"

namespace AlgebraicCurve
r2nos_namespace_dual

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTerm_eq_zero_of_adeleBdd_canonical
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleBdd (canonicalDivisorOf hω)) (v : Place K F) :
    kaehlerResidueTerm ω α v = 0 := by
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]

    have hαv : -(canonicalDivisorOf hω v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTerm_support_subset
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    Function.support (kaehlerResidueTerm ω α) ⊆ ↑(D - canonicalDivisorOf hω).support := by
  intro v hv

  rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply, ne_eq, sub_eq_zero]
  intro hDω
  apply hv
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]
    have hαv : -(D v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [hDω, canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTerm_support_finite
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    (Function.support (kaehlerResidueTerm ω α)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (kaehlerResidueTerm_support_subset hω hα)

theorem kaehlerResidueTerm_support_finite_of_adeleSpace
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    (Function.support (kaehlerResidueTerm ω α)).Finite := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact kaehlerResidueTerm_support_finite hω hD

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

variable (K F) in

def weilOfKaehler {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v
  map_add' α β := by
    have hsupα := kaehlerResidueTerm_support_finite_of_adeleSpace hω α.2
    have hsupβ := kaehlerResidueTerm_support_finite_of_adeleSpace hω β.2
    rw [← finsum_add_distrib hsupα hsupβ]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    unfold kaehlerResidueTerm
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

theorem weilOfKaehler_apply {ω : Ω[F⁄K]} (hω : ω ≠ 0) (α : adeleSpace K F) :
    weilOfKaehler K F hω α = ∑ᶠ v, kaehlerResidueTerm ω (α : Place K F → F) v := rfl

theorem weilOfKaehler_vanish_adeleBdd_canonical {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd (canonicalDivisorOf hω)) :
    weilOfKaehler K F hω α = 0 := by
  rw [weilOfKaehler_apply]
  exact finsum_eq_zero_of_forall_eq_zero
    (kaehlerResidueTerm_eq_zero_of_adeleBdd_canonical hω hα)

variable (K F)

def ResidueTheorem : Prop :=
  ∀ [HasPrincipalDivisors K F] {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F),
    weilOfKaehler K F hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0

variable {K F}

variable (K F)

def WeilKaehlerAgree : Prop :=
  ∀ [HasPrincipalDivisors K F] {ω : Ω[F⁄K]} (hω : ω ≠ 0),
    weilOfKaehler K F hω ≠ 0 ∧
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) ∧
    ∀ D : Divisor K F, weilOfKaehler K F hω ∈ omegaSpace D → D ≤ canonicalDivisorOf hω

variable {K F}

variable (K F)

def ResiduePairingSurjective : Prop :=
  ∀ [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (_hφ0 : φ ≠ 0)
    (_hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W),
    Function.Surjective (residuePairing K F W D hφ)

end AlgebraicCurve

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
