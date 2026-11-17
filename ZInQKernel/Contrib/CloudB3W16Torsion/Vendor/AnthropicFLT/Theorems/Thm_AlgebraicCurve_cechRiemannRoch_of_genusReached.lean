/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicCurve
theorem cechRiemannRoch_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached.solution
end AlgebraicCurve
