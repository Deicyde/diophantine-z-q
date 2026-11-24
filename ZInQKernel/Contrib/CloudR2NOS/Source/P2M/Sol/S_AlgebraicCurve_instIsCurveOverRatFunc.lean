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
  Source file    : P2M/Sol/S_AlgebraicCurve_instIsCurveOverRatFunc.lean
  Source sha256  : 4c94d66072086130056ac0f73042c9e59b365cbf846ea504e5c09447fa71e288
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 37 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 11 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option synthInstance.maxHeartbeats 1600000`; `set_option maxHeartbeats 3200000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 5 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
r2nos_erase_attr "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
w03_open "AlgebraicCurve"

scoped instance instHasPrincipalDivisorsRatFuncLaneB (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  RationalFunctionField.hasPrincipalDivisors K
end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero IsLocalRing"
open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
w03_open "AlgebraicCurve"

namespace Place
r2nos_namespace_dual
w03_export "AlgebraicCurve.Place" "ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite"
w03_open "AlgebraicCurve.Place"

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem finiteResidue_of_deg_pos (h : 0 < v.deg) : v.FiniteResidue :=
  ⟨Module.finite_of_finrank_pos h⟩
end DegPos
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
end Place
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
namespace RationalFunctionField
r2nos_namespace_dual
w03_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors"
w03_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]

scoped instance instFiniteResidueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).FiniteResidue := by
  obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
  refine Place.finiteResidue_of_deg_pos _ ?_
  rw [deg_ofHeightOneSpectrum K hw]
  exact hp.natDegree_pos

scoped instance instFiniteResiduePlaceInfty [DecidableEq (RatFunc K)] :
    (placeInfty K).FiniteResidue :=
  Place.finiteResidue_of_deg_pos _ (by rw [deg_placeInfty K]; exact one_pos)

variable {K} in

scoped instance instFiniteResidue (v : Place K (RatFunc K)) : v.FiniteResidue := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact instFiniteResidueOfHeightOneSpectrum K w
  · exact instFiniteResiduePlaceInfty K

end RationalFunctionField
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

namespace Place
r2nos_namespace_dual
w03_export "AlgebraicCurve.Place" "ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite"
w03_open "AlgebraicCurve.Place"

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')
end Restrict
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end Place
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential
r2nos_open_dual "KaehlerDifferential"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
w03_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}
namespace IsCurveOver
r2nos_namespace_dual
w03_export "AlgebraicCurve.IsCurveOver" "hasPrincipalDivisors instFiniteResidue finiteResidue kaehler_free_rank_one"
end IsCurveOver
r2nos_open_scoped "AlgebraicCurve.IsCurveOver" in

theorem IsCurveOver.of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

namespace RationalFunctionField
r2nos_namespace_dual
w03_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors"
w03_open "AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K]

theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ
end RationalFunctionField
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
variable (K F)
end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
section AxiomAudit
end AxiomAudit
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

section

set_option autoImplicit false

noncomputable section

w03_open "IntermediateField AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve Polynomial TensorProduct Module"


namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
w03_open "AlgebraicCurve"

variable (K : Type*) [Field K]

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=
  ⟨Module.Free.of_basis (kaehlerRatFuncBasis K),
    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩

scoped instance instIsCurveOverRatFunc : IsCurveOver K (RatFunc K) :=
  RationalFunctionField.isCurveOver_of_kaehlerRankOne K (kaehlerRankOne_ratFunc K)

variable {F : Type*} [Field F] [Algebra K F]
variable {K}
variable (K F)
variable {K F}
end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
namespace ModularCurve
r2nos_namespace_dual
w03_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
end ModularCurve
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
section Gates
w03_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.ModularCurve"
variable (K : Type*) [Field K]
end Gates
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
w03_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

theorem solution (K : Type*) [Field K] : AlgebraicCurve.IsCurveOver K (RatFunc K) :=
  AlgebraicCurve.instIsCurveOverRatFunc K
end
end
end
end S_AlgebraicCurve_instIsCurveOverRatFunc
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
