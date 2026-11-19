/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues (git blob c59cb611fcf9f62a427d405ecd6f8a62f5999579, sha256 cb46c8c521007e426e03e3faf6b3e96df6c562c185bfdc418701d97fd837270d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues
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
    [Module.Finite ℂ ↥(regularDifferentials ℂ F)]
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (S : Finset (Place ℂ F))
    (hS2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hS5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (𝒯 𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZall : ∀ (A : Type) [AddCommGroup A], ∀ f : 𝒟.ιE → A,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
    (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ 𝒟.skeleton)
    (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * 𝒟.edgeInt θ e)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
      let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
      let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
        ∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
              (i - wd.symm ⟨(e, true), he⟩).val <
                (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
          (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
          cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
              ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S) :
    ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral ϑ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) +
        2 * π * I * ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
  revert F hfg hF 𝒟 hvert S hS2 hS5 𝒯 𝒯s h𝒯s Z hZ hZall γ hγs hγi hWD Pt δ hδ
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.solution
