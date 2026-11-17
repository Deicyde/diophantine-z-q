/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential (git blob c94fcb5411c91e57f11c9f571998fef246dd7662, sha256 9e41830f4da6d95d7eb732247c4d04d8fc5c7959710453c4aa2051305f0e8f09).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential

set_option autoImplicit false

open AlgebraicCurve IntermediateField

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  haveI : PerfectField K := inferInstance
  haveI : v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver v

  obtain ⟨x, -, hfin, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := K) (F := F)).mp
      inferInstance
  haveI := hfin
  haveI : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite K⟮x⟯ F

  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  have hπ₀ : v.ord ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) = 1 :=
    v.ord_coe_irreducible hirr
  have hd : v.dCoord = KaehlerDifferential.D K F
      ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) := rfl
  have hω : ω = v.differentialCoeff ω • KaehlerDifferential.D K F
      ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) := by
    rw [← hd, v.differentialCoeff_smul_dCoord]
  rw [AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff x v hπ₀ ω]
  show _ = v.ord (v.differentialCoeff ω)
  conv_lhs => rw [hω]
  rw [AlgebraicCurve.Place.diffCoeff_smul_D_eq x v (by rw [hπ₀]; exact one_ne_zero)]
