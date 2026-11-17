/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CartesianMonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
    (k : Type u) [Field k] [IsAlgClosed k] (C Y Z : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] [IsProper Y.hom] [IsIntegral Y.left]
    [LocallyOfFiniteType Z.hom] [IsIntegral Z.left]
    (c₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
    (L : (C ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (lift (toUnit (Y ⊗ Z) ≫ c₀) (𝟙 (Y ⊗ Z)) : Y ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Z) (lift (toUnit (C ⊗ Z) ≫ y₀) (snd C Z)) : C ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Y) (lift (snd C Y) (toUnit (C ⊗ Y) ≫ z₀)) : C ⊗ Y ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one.solution
