/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact
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

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).Opens)
    (hW : IsCompact (W : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ W₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Opens,
        IsCompact (W₀ : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) ∧
        ∀ q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          q ≫ pullback.fst f _ = pullback.fst f _ →
          q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q ⁻¹ᵁ W₀ = W := by
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
  obtain ⟨i, W₀, hW₀c, hW₀⟩ :=
    exists_preimage_eq (SubalgebraStages.diagram S f) (SubalgebraStages.cone S f) hc W hW
  refine ⟨(Opposite.unop i).1, (Opposite.unop i).2.1, (Opposite.unop i).2.2, W₀, hW₀c, fun q hq₁ hq₂ => ?_⟩

  have hq : q = SubalgebraStages.leg S f (Opposite.unop i) := by
    apply pullback.hom_ext
    · rw [hq₁, SubalgebraStages.leg_fst]
    · rw [hq₂, SubalgebraStages.leg_snd]
  rw [hq]
  exact hW₀
