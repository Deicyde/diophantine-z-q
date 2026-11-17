/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_instIsCurveOverRatFunc (git blob a626ea2346647b89be38ad9307496d6d49c32be5, sha256 4c94d66072086130056ac0f73042c9e59b365cbf846ea504e5c09447fa71e288).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
end P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve.RationalFunctionField
end AlgebraicCurve.RationalFunctionField
namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
namespace AlgebraicCurve.IsCurveOver
end AlgebraicCurve.IsCurveOver
namespace IntermediateField
end IntermediateField
namespace Polynomial
end Polynomial
namespace TensorProduct
end TensorProduct
namespace Module
end Module
namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.ModularCurve
end P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.ModularCurve

namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors)
open _root_.AlgebraicCurve

scoped instance instHasPrincipalDivisorsRatFuncLaneB (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  RationalFunctionField.hasPrincipalDivisors K
end AlgebraicCurve
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite)
open _root_.AlgebraicCurve.Place

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem finiteResidue_of_deg_pos (h : 0 < v.deg) : v.FiniteResidue :=
  ⟨Module.finite_of_finrank_pos h⟩
end DegPos
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
end Place
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
namespace RationalFunctionField
export _root_.AlgebraicCurve.RationalFunctionField (exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors)
open _root_.AlgebraicCurve.RationalFunctionField
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
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField

namespace Place
export _root_.AlgebraicCurve.Place (ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite)
open _root_.AlgebraicCurve.Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')
end Restrict
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end Place
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end AlgebraicCurve
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors)
open _root_.AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}
namespace IsCurveOver export _root_.AlgebraicCurve.IsCurveOver (hasPrincipalDivisors instFiniteResidue finiteResidue kaehler_free_rank_one) end IsCurveOver
open scoped _root_.AlgebraicCurve.IsCurveOver in

theorem IsCurveOver.of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

namespace RationalFunctionField
export _root_.AlgebraicCurve.RationalFunctionField (exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors)
open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ
end RationalFunctionField
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
variable (K F)
end AlgebraicCurve
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
section AxiomAudit
end AxiomAudit
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField

section

set_option autoImplicit false

noncomputable section

open _root_.IntermediateField
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
open _root_.Polynomial
open _root_.TensorProduct
open _root_.Module

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors)
open _root_.AlgebraicCurve

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
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
namespace ModularCurve
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
end ModularCurve
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
section Gates
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.ModularCurve
variable (K : Type*) [Field K]
end Gates
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField
end
open scoped _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField

theorem solution (K : Type*) [Field K] : AlgebraicCurve.IsCurveOver K (RatFunc K) :=
  AlgebraicCurve.instIsCurveOverRatFunc K
