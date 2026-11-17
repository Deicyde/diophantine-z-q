/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_charP_residueField_of_liesOverPrime (git blob 757601318e3352941ab7e723f2203a831ced6d59, sha256 2a377cc5997bd972132034e1a5114b3d6c275b4914190cfbaa9a1390057bbf13).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Flat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_FibreModel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_IgusaScheme
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_charP_residueField_of_liesOverPrime
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct
noncomputable section

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (ResidueField ↥A) ℓ := by
  have hp : (ℓ : ℕ).Prime := Fact.out
  have hval : A.valuation (ℓ : AlgebraicClosure ℚ) < 1 := lt_of_le_of_ne hA.1 (fun h => hA.2 h.ge)
  have hcast : ((ℓ : ↥A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by push_cast; ring
  have hnu : ¬ IsUnit (ℓ : ↥A) := by
    intro hu
    have := A.valuation_unit hu.unit
    rw [IsUnit.unit_spec, hcast] at this
    exact absurd this.ge hA.2
  have hmem : (ℓ : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hnu
  have hzero : (ℓ : ResidueField ↥A) = 0 := by
    rw [← map_natCast (residue ↥A)]; exact (residue_eq_zero_iff _).mpr hmem
  have hrc : ringChar (ResidueField ↥A) ∣ ℓ := (ringChar.spec _ ℓ).mp hzero
  have hrcℓ : ringChar (ResidueField ↥A) = ℓ :=
    (hp.eq_one_or_self_of_dvd _ hrc).resolve_left (CharP.ringChar_ne_one (R := ResidueField ↥A))
  exact hrcℓ ▸ ringChar.charP (ResidueField ↥A)
