import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Transfer of the ACTUAL kernel comparison through a universal model

Kernel comparison is natural in a commuting square. Consequently, an actual
model map that is an iso on degree-zero kernels before and after base change
transfers the canonical kernel-comparison isomorphism to the model's target.
No arbitrary object isomorphism is substituted for either kernel map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The canonical kernel comparison transfers along an actual commuting model
map whose kernel maps before and after base change are isomorphisms. -/
theorem isIso_kernelComparison_of_universal_model_map
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasKernels C] [HasKernels D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f')
    (ha : IsIso (kernel.map f f' a b h))
    (hFa : IsIso (kernel.map (F.map f) (F.map f') (F.map a) (F.map b)
      (by rw [← F.map_comp, ← F.map_comp, h])))
    (hFf : IsIso (kernelComparison f F)) :
    IsIso (kernelComparison f' F) := by
  haveI := ha
  haveI := hFa
  haveI := hFf
  have hc := kernelComparison_comp_kernel_map f F f' a b h
  haveI : IsIso (F.map (kernel.map f f' a b h) ≫ kernelComparison f' F) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (kernel.map f f' a b h)) (kernelComparison f' F)

/-- An actual quasi-isomorphism of nonnegative complexes is an isomorphism on
cycles in degree zero, canonically through the homology projection. -/
theorem isIso_cyclesMap_zero_of_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ] :
    IsIso (HomologicalComplex.cyclesMap φ 0) := by
  haveI : IsIso (HomologicalComplex.homologyMap φ 0) := inferInstance
  have h := HomologicalComplex.homologyπ_naturality φ 0
  haveI : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right (HomologicalComplex.cyclesMap φ 0) (L.homologyπ 0)

/-- The actual degree-zero cycles are canonically the kernel of d0. -/
@[simps]
def cyclesKernelZeroIso {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℕ) : K.cycles 0 ≅ kernel (K.d 0 1) where
  hom := kernel.lift (K.d 0 1) (K.iCycles 0) (K.iCycles_d 0 1)
  inv := K.liftCycles (kernel.ι (K.d 0 1)) 1 (by simp) (kernel.condition _)
  hom_inv_id := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (K.d 0 1))).mp
    simp only [Category.assoc, kernel.lift_ι, HomologicalComplex.liftCycles_i, Category.id_comp]

/-- An actual quasi-isomorphism of nonnegative complexes is an isomorphism on
the kernel of d0. This applies both to the model map and each scalar extension. -/
theorem isIso_kernelMap_zero_of_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ] :
    IsIso (kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm) := by
  haveI := isIso_cyclesMap_zero_of_quasiIso φ
  let eK := cyclesKernelZeroIso K
  let eL := cyclesKernelZeroIso L
  have hc : eK.hom ≫ kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm =
      HomologicalComplex.cyclesMap φ 0 ≫ eL.hom := by
    apply (cancel_mono (kernel.ι (L.d 0 1))).mp
    simp only [Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc,
      eK, eL, cyclesKernelZeroIso_hom]
    exact (HomologicalComplex.cyclesMap_i φ 0).symm
  haveI : IsIso (eK.hom ≫ kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_left eK.hom _

end ZInQ.Contrib.CloudR2Poincare.L1
