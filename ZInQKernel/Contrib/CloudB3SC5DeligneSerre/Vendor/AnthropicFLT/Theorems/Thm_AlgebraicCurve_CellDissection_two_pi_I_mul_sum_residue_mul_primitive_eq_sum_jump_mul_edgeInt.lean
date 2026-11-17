/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt (git blob 3327a1f3d9b33c41ee2210adcee9f9657eb7a22e, sha256 b9c42512504a4c4da3cb73f0930c2acbbff6096ef3856c67ef54a23374770f6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (𝒟 : CellDissection F) (poles : Finset (Place ℂ F)) (c : Place ℂ F → 𝒟.ιC)
    (hc : ∀ v ∈ poles, v ∈ (𝒟.cell (c v)).interior')
    (θ : Ω[F⁄ℂ]) (hθpol : ∀ v ∈ poles, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q : Place ℂ F, Q ∉ poles → 0 ≤ Q.ordDifferential θ)
    (η : Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (hΨ : ∀ C, ∀ w ∈ V C, HasDerivAt (Ψ C) (coeffIn (𝒟.cell C).ζ η w) w) :
    ∃ J : 𝒟.ιE → ℂ,
      (∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e) ∧
      2 * π * I * ∑ v ∈ poles,
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ (c v) ((𝒟.cell (c v)).ζ v) =
        ∑ e : 𝒟.ιE, J e * 𝒟.edgeInt θ e := by
  revert F hfg hF 𝒟 poles c hc θ hθpol hθreg η V hV hKV hVt Ψ hΨ
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt.solution
