/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental (git blob 116a331d7ab1cec986635fae8307f73159208afe, sha256 5723f1041029e5612dda6ec16d559d75dba7aac43c43f13e5918019bb2f934d2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ConstantsAreBase K F := by

  haveI hICO : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx

  obtain ⟨t, htr_t, hfd_t, hsep_t⟩ :=
    exists_separating_transcendental_of_perfectField (K := K) (F := F) hx inferInstance
  haveI : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfd_t
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := hsep_t

  have hxIC : x ∉ (integralClosure K F).toSubring := fun h ↦ hx h.isAlgebraic

  obtain ⟨V, hICV, hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure K F).toSubring) hxIC

  have hKV : ∀ a : K, (RingHom.id F) (algebraMap K F a) ∈ V := fun a ↦
    hICV (Subalgebra.algebraMap_mem (integralClosure K F) a)

  obtain ⟨v₀, -⟩ :=
    Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (K := K) (F := F) (F' := F)
      t (RingHom.id F) V hKV ⟨x, hxV⟩

  exact constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
