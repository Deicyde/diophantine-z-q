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
  Source file    : Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean
  Source sha256  : 6b3882037276509e079ba3d5351afc7d6fab19f465d4e80bc31c4cc5f5c457af
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing
r2nos_open_dual "Polynomial IsDedekindDomain WithZero IsLocalRing"
open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

namespace AlgebraicCurve
r2nos_namespace_dual

namespace RationalFunctionField
r2nos_namespace_dual

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

instance instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions :
    Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

theorem placeInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty

variable {K}

theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

variable (K)

theorem placeOfPoint_ne_placeInfty [DecidableEq (RatFunc K)] (a : K) :
    placeOfPoint K a ≠ placeInfty K := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum]
  exact fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]; exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩
  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, placeOfPoint_eq_ofHeightOneSpectrum]

theorem eq_placeOfPoint_or_eq_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, hw⟩ | hw
  · obtain ⟨a, ha⟩ := exists_eq_placeOfPoint K w
    exact Or.inl ⟨a, hw.trans ha⟩
  · exact Or.inr hw

private def ofOption [DecidableEq (RatFunc K)] : Option K → Place K (RatFunc K) :=
  fun o => o.elim (placeInfty K) (placeOfPoint K)

private theorem ofOption_bijective [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Function.Bijective (ofOption K) := by
  constructor
  · rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (placeOfPoint_ne_placeInfty K b)
    · exact absurd h (placeOfPoint_ne_placeInfty K a)
    · exact congrArg some (placeOfPoint_injective K h)
  · intro v
    rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨a, ha⟩ | ha
    · exact ⟨some a, ha.symm⟩
    · exact ⟨none, ha.symm⟩

def placeEquivOption [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Place K (RatFunc K) ≃ Option K :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm

@[simp]
theorem placeEquivOption_symm_some [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    (placeEquivOption K).symm (some a) = placeOfPoint K a := rfl

@[simp]
theorem placeEquivOption_symm_none [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    (placeEquivOption K).symm none = placeInfty K := rfl

@[simp]
theorem placeEquivOption_placeOfPoint [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    placeEquivOption K (placeOfPoint K a) = some a :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm_apply_apply (some a)

@[simp]
theorem placeEquivOption_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    placeEquivOption K (placeInfty K) = none :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm_apply_apply none

end RationalFunctionField

end AlgebraicCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
