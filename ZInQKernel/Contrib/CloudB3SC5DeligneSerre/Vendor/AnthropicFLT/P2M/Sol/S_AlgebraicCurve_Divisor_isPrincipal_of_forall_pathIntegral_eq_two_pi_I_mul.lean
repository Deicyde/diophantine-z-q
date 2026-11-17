/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul (git blob 95a7597af7518033ff8b46f12853d9e72e7436b6, sha256 038ee1b6e8c10c8e9ecee08e2752487c9bad1951f9d91b304d4f71a59b8c89ff).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul.AlgebraicCurve
namespace Filter
end Filter
namespace Topology
end Topology

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul.AlgebraicCurve
open _root_.Filter
open _root_.Topology
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.IsPrincipal IsCurveOver Place.evalAt pathIntegral exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul exists_eventuallyEq_evalAt_of_meromorphicAt)
namespace LogDifferentialPrincipalProof
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end AlgebraicCurve.LogDifferentialPrincipalProof

open AlgebraicCurve.LogDifferentialPrincipalProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m) :
    Divisor.IsPrincipal D := by

  obtain ⟨g, hg⟩ :=
    AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul F hfg hF D
      θ hθ hres hper

  obtain ⟨f, hf⟩ :=
    AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt F hfg hF g fun v => (hg v).1

  have hf0 : f ≠ 0 := by
    intro hf0
    obtain ⟨v⟩ := (inferInstance : Nonempty (Place ℂ F))
    have hzero : (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
        =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)] 0 := by
      filter_upwards [hf v] with z hz
      rw [hz, hf0, Pi.zero_apply]
      exact evalAt_zero _
    have htop : meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
        (extChartAt 𝓘(ℂ, ℂ) v v) = ⊤ :=
      (meromorphicOrderAt_eq_top_iff).2 hzero
    rw [(hg v).2] at htop
    exact WithTop.coe_ne_top htop
  refine ⟨f, hf0, fun v => ?_⟩

  have h1 := (hg v).2
  rw [meromorphicOrderAt_congr (hf v), (hF f hf0 v).2] at h1
  exact_mod_cast h1.symm
