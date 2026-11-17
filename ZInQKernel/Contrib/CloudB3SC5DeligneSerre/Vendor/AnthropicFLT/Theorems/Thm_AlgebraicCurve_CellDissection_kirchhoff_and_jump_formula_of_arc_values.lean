/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values (git blob 1daa6ee0fead022b605c4996d3d4f4196b67ac1a, sha256 12b480127b04dbb48d4118746629bbe4318159be90c8763d7d619e980beaed9d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.kirchhoff_and_jump_formula_of_arc_values
    {F : Type u} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) (𝔸 : Type) [AddCommGroup 𝔸]
    (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N)
    (𝒯 𝒯s : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (m : ℕ) [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) :
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
      ∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
            (i - wd.symm ⟨(e, true), he⟩).val <
              (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
        (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
    (∀ p, B p - A p =
      if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1) →
    (∀ C, Function.Bijective (rot C)) →
    (∀ C k, endV (𝒟.side C k) = startV (𝒟.side C (rot C k))) →
    (∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩) →
    (∀ e, J e = B (𝒟.arcOf (e, true)) - A (𝒟.arcOf (e, false))) →
    (∀ e, J e = A (𝒟.arcOf (e, true)) - B (𝒟.arcOf (e, false))) →
    (∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => startV (𝒟.side C k)) →
    (∀ e ∈ 𝒯s, J e = 0) →
    (∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ f : 𝒟.ιE → 𝔸,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
        cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
            ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
          (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
    (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
      J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, pe j hj l • ∑ e, Z l e • I e) ∧
    ∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ, J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, n l • ∑ e, Z l e • I e := by
  revert F 𝒟 𝔸 A B I J rot 𝒯 𝒯s Z m wd
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.solution
