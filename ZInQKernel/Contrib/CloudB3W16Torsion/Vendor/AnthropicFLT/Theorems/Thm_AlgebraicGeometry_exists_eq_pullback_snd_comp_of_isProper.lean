/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_eq_pullback_snd_comp_of_isProper
    {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
    (z : Z ⟶ Spec (CommRingCat.of K))
    [IsProper x] [IsIntegral X] [IsIntegral Y] [IsSeparated z]
    [LocallyOfFiniteType y] [LocallyOfFiniteType z] [IsReduced (pullback x y)]
    (f : pullback x y ⟶ Z) (hf : f ≫ z = pullback.fst x y ≫ x)
    (y₀ : Spec (CommRingCat.of K) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _)
    (z₀ : Spec (CommRingCat.of K) ⟶ Z)
    (h : pullback.lift (𝟙 X) (x ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀,
      Category.comp_id]) ≫ f = x ≫ z₀) :
    ∃ g : Y ⟶ Z, f = pullback.snd x y ≫ g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper.solution
