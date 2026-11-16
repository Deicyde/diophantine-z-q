/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.HopfAlgebra.Basic
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero

set_option maxHeartbeats 3200000

attribute [local instance] Ideal.Quotient.field

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by

  haveI : Algebra.FiniteType K A := inferInstance

  haveI : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero K A

  haveI : IsArtinianRing A := .of_finite K A
  haveI : Finite (MaximalSpectrum A) := inferInstance

  have hI (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) := by
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite K (A ⧸ I.asIdeal) := Module.Finite.quotient K _
    haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsSeparable K (A ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyEtale.of_isSeparable K (A ⧸ I.asIdeal)
  refine ⟨?_, ?_⟩
  ·
    exact Algebra.FormallyEtale.of_equiv
      ((IsArtinianRing.equivPi A).restrictScalars K).symm
  ·
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
