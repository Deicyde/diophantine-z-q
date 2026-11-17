import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Canonical kernel base change for a split differential

This proves that the CANONICAL kernel comparison map is an isomorphism under
an arbitrary additive functor when the source kernel has a contracting
complement. It does not replace that map by an arbitrarily chosen isomorphism.
For degree-zero finite-free cohomology, this is the algebraic base-change step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Contracting splitting data make the canonical kernel comparison invertible
under every additive functor, without assuming that functor is left exact. -/
theorem isIso_kernelComparison_of_contracting_split
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasKernels C] [HasKernels D]
    (F : C ⥤ D) [F.Additive]
    {H X Y : C} (f : X ⟶ Y) (i : H ⟶ X) (p : X ⟶ H) (τ : Y ⟶ X)
    (hi : i ≫ f = 0) (hsum : p ≫ i + f ≫ τ = 𝟙 X) :
    IsIso (kernelComparison f F) := by
  let ki : H ⟶ kernel f := kernel.lift f i hi
  have hretract : kernel.ι f ≫ p ≫ ki = 𝟙 (kernel f) := by
    apply (cancel_mono (kernel.ι f)).1
    simp only [ki, Category.assoc, kernel.lift_ι, Category.id_comp]
    have h := kernel.ι f ≫= hsum
    simpa only [Preadditive.comp_add, Category.assoc, kernel.condition_assoc,
      zero_comp, add_zero, Category.comp_id] using h
  have hsumF : F.map p ≫ F.map i + F.map f ≫ F.map τ = 𝟙 (F.obj X) := by
    calc
      F.map p ≫ F.map i + F.map f ≫ F.map τ = F.map (p ≫ i + f ≫ τ) := by
        rw [F.map_add, F.map_comp, F.map_comp]
      _ = F.map (𝟙 X) := congrArg (fun u : X ⟶ X ↦ F.map u) hsum
      _ = 𝟙 (F.obj X) := F.map_id X
  let v : kernel (F.map f) ⟶ F.obj (kernel f) :=
    kernel.ι (F.map f) ≫ F.map p ≫ F.map ki
  refine ⟨⟨v, ?_, ?_⟩⟩
  · change kernelComparison f F ≫ (kernel.ι (F.map f) ≫ F.map p ≫ F.map ki) = _
    rw [← Category.assoc, ← Category.assoc, kernelComparison_comp_ι,
      ← Functor.map_comp, ← Functor.map_comp, Category.assoc, hretract, F.map_id]
  · apply (cancel_mono (kernel.ι (F.map f))).1
    dsimp only [v]
    rw [Category.assoc, kernelComparison_comp_ι]
    simp only [Category.assoc, Category.id_comp]
    rw [← Functor.map_comp]
    dsimp only [ki]
    rw [kernel.lift_ι]
    have h := kernel.ι (F.map f) ≫= hsumF
    simpa only [Preadditive.comp_add, Category.assoc, kernel.condition_assoc,
      zero_comp, add_zero, Category.comp_id, Category.id_comp] using h

end ZInQ.Contrib.CloudR2Poincare.L1
