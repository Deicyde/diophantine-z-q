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
  Source file    : P2M/Sol/S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.lean
  Source sha256  : 837ea9f92e6a8b83179079532975c013cec88db2fd5358b43b91a9b0aa5f5ce0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

w03_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.AlgebraicCurve"
open IsDedekindDomain WithZero IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero IsLocalRing"
open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Place.deg Place.ofHeightOneSpectrum Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum"
namespace RationalFunctionField
r2nos_namespace_dual
w03_open "AlgebraicCurve"

namespace WFf
r2nos_namespace_dual
variable (K : Type*) [Field K]

theorem algebraMap_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring :=
  (Place.mem_iff_adicValuation_le_one _).mpr
    ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mp (w.valuation_le_one q))

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

theorem residueOfHeightOneSpectrum_apply (w : HeightOneSpectrum K[X]) (q : K[X]) :
    residueOfHeightOneSpectrum K w q = IsLocalRing.residue _
      ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_ofHeightOneSpectrum K w q⟩ := rfl

theorem ker_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    RingHom.ker (residueOfHeightOneSpectrum K w) = w.asIdeal := by
  ext q
  rw [RingHom.mem_ker, residueOfHeightOneSpectrum_apply, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w q

theorem surjective_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    Function.Surjective (residueOfHeightOneSpectrum K w) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
  have hxval : w.valuation (RatFunc K) x ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hx)
  have hden_ne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr x.denom_ne_zero
  have hmul : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num :=
    ((div_eq_iff hden_ne).mp x.num_div_denom).symm
  have hden : x.denom ∉ w.asIdeal := by
    intro hd
    have hnum : x.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom x
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num)
        = w.valuation (RatFunc K) x
            * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) :=
          mul_le_of_le_one_left' hxval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w x.denom).mpr hd
  have hmax : w.asIdeal.IsMaximal := IsPrime.to_maximal_ideal w.ne_bot
  obtain ⟨t, ht⟩ : ∃ t : K[X], x.denom * t - 1 ∈ w.asIdeal := by
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv hden
    refine ⟨b, ?_⟩
    rw [show x.denom * b - 1 = -c by linear_combination hbc]
    exact neg_mem hc
  refine ⟨x.num * t, ?_⟩
  rw [residueOfHeightOneSpectrum_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  show (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).adicValuation
    (algebraMap K[X] (RatFunc K) (x.num * t) - x) < 1
  rw [← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  have key : algebraMap K[X] (RatFunc K) (x.num * t) - x
      = x * algebraMap K[X] (RatFunc K) (x.denom * t - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hmul]
  rw [key, map_mul]
  calc w.valuation (RatFunc K) x
        * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1))
      ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1)) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr ht

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

end WFf

end AlgebraicCurve.RationalFunctionField

end

theorem solution (K : Type*) [Field K] {w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)} {p : Polynomial K} (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by
  rw [Place.deg, ← (AlgebraicCurve.RationalFunctionField.WFf.residueFieldEquivOfHeightOneSpectrum K
    w).toLinearEquiv.finrank_eq, hw]
  exact finrank_quotient_span_eq_natDegree
end S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
