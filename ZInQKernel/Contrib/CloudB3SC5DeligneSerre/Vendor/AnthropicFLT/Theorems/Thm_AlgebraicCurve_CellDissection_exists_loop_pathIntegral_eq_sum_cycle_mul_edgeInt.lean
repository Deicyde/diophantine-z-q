/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt (git blob fecfc9933881d0122149c548060f10fa2ad3847d, sha256 8f9b4ae92e7a3dd3feefbca225055687fd33ca30e21ea0a4d7ba08a2894f43f5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
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
    (𝒟 : CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZk : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e)
    (hZd : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0)
    (hZ0 : ∀ j ∈ 𝒯, Z j = 0)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    (j : 𝒟.ιE) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ 𝒟.skeleton) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * 𝒟.edgeInt θ e := by
  revert F hfg hF 𝒟 𝒯 Z hZk hZd hZ0 h𝒯path hwalk j
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.solution
