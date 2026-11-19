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
  Source file    : P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean
  Source sha256  : a9a0efe90ae30e6e3d0905b9ec079f1e8d1102d30a1f4fd2ce4797ab3e431e57
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 10 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.FieldTheory.RatFunc.Degree
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

w03_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.AlgebraicCurve"
open IsDedekindDomain WithZero IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero IsLocalRing"
open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff"
namespace RationalFunctionField
r2nos_namespace_dual
w03_export "AlgebraicCurve.RationalFunctionField" "exists_forall_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum ord_ofHeightOneSpectrum_of_span ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_eq_one_of_forall_ne_ofHeightOneSpectrum"
w03_open "AlgebraicCurve.RationalFunctionField~finitePlace~heightOneSpectrumOfIrreducible_asIdeal~heightOneSpectrumOfIrreducible AlgebraicCurve"

namespace WFj
r2nos_namespace_dual
variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

theorem heightOneSpectrumOfIrreducible_asIdeal {p : K[X]} (hp : Irreducible p) :
    (heightOneSpectrumOfIrreducible K hp).asIdeal = Ideal.span {p} := rfl

def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

variable {K}

theorem ne_finitePlace_of_forall_ne {v : Place K (RatFunc K)}
    (hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w) {p : K[X]} (hp : Irreducible p) :
    v ≠ finitePlace K hp :=
  hv _

theorem single_add_single_apply_eq_ord {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  by_cases hfin : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hfin

    rw [Finsupp.single_eq_of_ne (hvinf w).symm, add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      symm
      by_contra hne
      refine hcase ?_
      have hmem : p ∈ w.asIdeal :=
        (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp0).mp hne
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp]
      rfl
  ·
    have hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w :=
      fun w h => hfin ⟨w, h⟩
    have hveq : v = vinf := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv hvinf
    rw [Finsupp.single_eq_of_ne (show v ≠ finitePlace K hp from hv _), zero_add, hveq,
      Finsupp.single_eq_same,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum vinf hvinf (RatFunc.algebraMap_ne_zero hp0),
      RatFunc.intDegree_polynomial]

theorem degree_single_add_single {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single,
    show (finitePlace K hp).deg = p.natDegree from
      deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp),
    deg_eq_one_of_forall_ne_ofHeightOneSpectrum vinf hvinf]
  push_cast
  ring

end WFj

end AlgebraicCurve.RationalFunctionField

end

theorem solution {K : Type*} [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K), (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) → Divisor.degree D = 0 := by
  classical
  obtain ⟨vinf, hvinf⟩ := AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : (algebraMap K[X] (RatFunc K)) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [hD v, hC, v.ord_algebraMap]
      simp
    rw [hzero, map_zero]
  · intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (AlgebraicCurve.RationalFunctionField.WFj.finitePlace K hp.irreducible) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ)) with hDp_def
    have hDp : ∀ v : Place K (RatFunc K), Dp v = v.ord (algebraMap K[X] (RatFunc K) p) :=
      fun v => AlgebraicCurve.RationalFunctionField.WFj.single_add_single_apply_eq_ord hvinf
        hp.irreducible v
    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp v, map_mul, v.ord_mul hp' ha']
      ring
    have hdeg_p : Divisor.degree Dp = 0 :=
      AlgebraicCurve.RationalFunctionField.WFj.degree_single_add_single hvinf hp.irreducible
    have hdeg_a : Divisor.degree (D - Dp) = 0 := ih (D - Dp) hDa
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hdeg_p, zero_add]
    exact hdeg_a
end S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
