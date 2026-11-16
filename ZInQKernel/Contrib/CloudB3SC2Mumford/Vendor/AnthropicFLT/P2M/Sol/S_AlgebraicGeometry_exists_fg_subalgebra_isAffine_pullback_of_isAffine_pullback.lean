/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open _root_.AlgebraicGeometry.SubalgebraStages in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by
  classical

  let ι : Type u := {T : Subalgebra A₀ A // T.FG ∧ (↑s : Set A) ⊆ T}
  haveI : Nonempty ι := ⟨⟨Algebra.adjoin A₀ ↑s, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin⟩⟩
  haveI : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1, T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra A₀ A := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ a : A, ∃ i, a ∈ S i := fun a =>
    ⟨⟨Algebra.adjoin A₀ ↑(insert a s), Subalgebra.fg_adjoin_finset _,
        fun x hx => Algebra.subset_adjoin (by simp [hx])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS f
  haveI : IsAffine (cone S f).pt :=
    ‹IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))›
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit (diagram S f) (cone S f) hc
  exact ⟨(Opposite.unop i).1, (Opposite.unop i).2.1, (Opposite.unop i).2.2, hi⟩
