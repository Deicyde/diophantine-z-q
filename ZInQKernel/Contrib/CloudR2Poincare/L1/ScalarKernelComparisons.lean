import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Canonical kernels through flat localization and scalar extension composition

All comparison morphisms remain the actual canonical kernel maps. The flat
extension statement is proved with tensor exactness and the concrete kernel
universal property; the other statements are canonical comparison naturality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The actual canonical kernel comparison for a composite is the composition
of its two actual comparisons. -/
theorem kernelComparison_comp_functor
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    [HasKernels C] [HasKernels D] [HasKernels E]
    {X Y : C} (f : X ⟶ Y) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    kernelComparison f (F ⋙ G) = G.map (kernelComparison f F) ≫ kernelComparison (F.map f) G := by
  apply (cancel_mono (kernel.ι (G.map (F.map f)))).mp
  simp only [Category.assoc, kernelComparison_comp_ι, Functor.comp_map]
  rw [← G.map_comp, kernelComparison_comp_ι]
  exact kernelComparison_comp_ι f (F ⋙ G)

/-- Kernel-comparison invertibility is invariant under a natural isomorphism
of the base-change functor. -/
theorem isIso_kernelComparison_of_functor_iso
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasKernels C] [HasKernels D]
    {X Y : C} (f : X ⟶ Y) (F G : C ⥤ D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (η : F ≅ G) (hF : IsIso (kernelComparison f F)) :
    IsIso (kernelComparison f G) := by
  haveI := hF
  have h : kernelComparison f F ≫
      kernel.map (F.map f) (G.map f) (η.app X).hom (η.app Y).hom (η.hom.naturality f) =
      (η.app (kernel f)).hom ≫ kernelComparison f G := by
    apply (cancel_mono (kernel.ι (G.map f))).mp
    simp only [Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc,
      kernelComparison_comp_ι, kernelComparison_comp_ι_assoc, Iso.app_hom]
    exact η.hom.naturality (kernel.ι f)
  haveI : IsIso ((η.app (kernel f)).hom ≫ kernelComparison f G) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (η.app (kernel f)).hom (kernelComparison f G)

/-- A flat scalar extension preserves the ACTUAL canonical kernel comparison. -/
theorem isIso_kernelComparison_extendScalars_of_flat
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso (kernelComparison f (ModuleCat.extendScalars (algebraMap R S))) := by
  let A := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let e : A ≃ₗ[R] S :=
    { toFun := fun s ↦ s
      invFun := fun s ↦ s
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ by
        change (algebraMap R S r * (show S from s) : S) = r • (show S from s)
        rw [Algebra.smul_def] }
  haveI : Module.Flat R A := Module.Flat.of_linearEquiv e
  let F := ModuleCat.extendScalars (algebraMap R S)
  have hker : (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)
  have hex : Function.Exact ((F.map (kernel.ι f)).hom) (F.map f).hom := by
    change Function.Exact ((kernel.ι f).hom.lTensor A) (f.hom.lTensor A)
    exact Module.Flat.lTensor_exact A
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hker)
  have hinj : Function.Injective (F.map (kernel.ι f)).hom := by
    change Function.Injective ((kernel.ι f).hom.lTensor A)
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  haveI : Mono (F.map (kernel.ι f)) := (ModuleCat.mono_iff_injective _).mpr hinj
  let Q := ShortComplex.mk (F.map (kernel.ι f)) (F.map f)
    (by rw [← F.map_comp, kernel.condition, F.map_zero])
  have hQ : Q.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex
  let hk := hQ.fIsKernel
  let iso := IsLimit.conePointUniqueUpToIso hk (kernelIsKernel (F.map f))
  have hfac : iso.hom ≫ kernel.ι (F.map f) = F.map (kernel.ι f) :=
    IsLimit.conePointUniqueUpToIso_hom_comp hk (kernelIsKernel (F.map f)) WalkingParallelPair.zero
  have heq : kernelComparison f F = iso.hom := by
    apply (cancel_mono (kernel.ι (F.map f))).mp
    exact (kernelComparison_comp_ι f F).trans hfac.symm
  rw [heq]
  infer_instance

end ZInQ.Contrib.CloudR2Poincare.L1
