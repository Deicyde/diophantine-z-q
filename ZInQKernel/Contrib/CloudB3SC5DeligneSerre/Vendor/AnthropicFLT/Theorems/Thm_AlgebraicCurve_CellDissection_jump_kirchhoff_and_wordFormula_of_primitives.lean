/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives (git blob 1c55a704a5cda722020643c38dcf337a5529f273, sha256 cfc5181174d9488dd4ea76897b37f531af7320c0544f3815b3ca0cbe6ce7b900).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives
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
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (κ : Type*) [Fintype κ]
    (η : κ → Ω[F⁄ℂ]) (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i))
    (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)
    (hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w)
    (J : 𝒟.ιE → κ → ℂ)
    (hJ : ∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i)
    (𝒯 𝒯s : Finset 𝒟.ιE) (hJ0 : ∀ e ∈ 𝒯s, J e = 0) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZ' : ∀ f : 𝒟.ιE → κ → ℂ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
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
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) :
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ,
      J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (n l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e) ∧
    ∀ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
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
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
      (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
      ∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
        J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (pe j hj l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e := by
  revert F hfg hF 𝒟 hvert κ η hη V hV hKV hVt Ψ hΨ J hJ 𝒯 𝒯s hJ0 Z hZ hZ' hWD
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.solution
