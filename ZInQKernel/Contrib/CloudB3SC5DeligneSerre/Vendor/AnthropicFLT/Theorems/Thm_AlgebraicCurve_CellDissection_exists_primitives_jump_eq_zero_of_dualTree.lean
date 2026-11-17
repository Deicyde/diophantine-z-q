/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree (git blob 03e51eba856154281de1e2323f8474856d5ac20e, sha256 a470c480f1ccc943f1fa12832d0c553451dca860e62d5115d335eb82a4cf1f80).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_primitives_jump_eq_zero_of_dualTree
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
    (𝒟 : CellDissection F) (κ : Type*) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) (w₀ : ℂ) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      (∀ C, IsOpen (V C)) ∧ (∀ C, (𝒟.cell C).R.K ⊆ V C) ∧ (∀ C, V C ⊆ (𝒟.cell C).ζ.target) ∧
      (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w) ∧
      (∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i) ∧
      (∀ e ∈ 𝒯s, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  revert F hfg hF 𝒟 κ η hη 𝒯s h𝒯s C₀ w₀
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.solution
