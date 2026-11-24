import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.OriginalKernelConsumer
import ZInQKernel.Contrib.CloudB3W17bKernel.KernelMap

/-!
The graph formula is derived from the SAME original native differenceHom and
the actual reduced closed support's kernel formula. Group structure and point
lifting are constructed by existing consumers, never supplied as graph models.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)
open ZInQ.Contrib.CloudB3W17GAGA (APts)
open ZInQ.Contrib.CloudB3W17bKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

noncomputable section
namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- The actual support-kernel formula yields the ORIGINAL graph lifting formula. -/
theorem original_kernel_graph_iff (A B : AbVar ℂ) (F : APts A →* APts B)
    (Z : Closeds (A.X ⊗ B.X).left)
    (hker : ∀ R : APts (AVGlue.prodAbVar A B),
      differenceHom A B F R = 1 ↔ R.left (IsLocalRing.closedPoint ℂ) ∈ Z)
    (P : APts A) (Q : APts B) :
    F P = Q ↔ ∃ t : cptObj (RingHom.id ℂ) ⟶ reducedClosedOver (A.X ⊗ B.X) Z,
      t ≫ (reducedClosedι (A.X ⊗ B.X) Z ≫ fst A.X B.X) = P ∧
      t ≫ (reducedClosedι (A.X ⊗ B.X) Z ≫ snd A.X B.X) = Q := by
  rw [graph_iff_exists_kernelPoint A B F P Q]
  constructor
  · rintro ⟨R, hR, hP, hQ⟩
    obtain ⟨t, ht⟩ := (originalPoint_mem_iff_lift_reducedClosed (A.X ⊗ B.X) Z R).mp
      ((hker R).mp hR)
    refine ⟨t, ?_, ?_⟩
    · simpa only [Category.assoc] using
        (congrArg (fun R => R ≫ fst A.X B.X) ht).trans hP
    · simpa only [Category.assoc] using
        (congrArg (fun R => R ≫ snd A.X B.X) ht).trans hQ
  · rintro ⟨t, htP, htQ⟩
    let R : APts (AVGlue.prodAbVar A B) := t ≫ reducedClosedι (A.X ⊗ B.X) Z
    have hR : differenceHom A B F R = 1 := (hker R).mpr
      ((originalPoint_mem_iff_lift_reducedClosed (A.X ⊗ B.X) Z R).mpr ⟨t, rfl⟩)
    exact ⟨R, hR, by simpa only [R, Category.assoc] using htP,
      by simpa only [R, Category.assoc] using htQ⟩

/-- Original point realization follows from the exact actual differenceHom-kernel
support; neither a kernel group nor an algebraic graph is assumed. -/
theorem exists_scheme_realization_of_original_kernel_support
    (A B : AbVar ℂ) (F : APts A →* APts B) (Z : Closeds (A.X ⊗ B.X).left)
    (hker : ∀ R : APts (AVGlue.prodAbVar A B),
      differenceHom A B F R = 1 ↔ R.left (IsLocalRing.closedPoint ℂ) ∈ Z) :
    ∃ f : A.X ⟶ B.X, ∀ P : APts A, F P = P ≫ f := by
  haveI : LocallyOfFiniteType (A.X ⊗ B.X).hom := by
    change LocallyOfFiniteType (pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    infer_instance
  letI := reducedClosedOriginalKernelGrp (A.X ⊗ B.X) Z (differenceHom A B F) hker
  letI := isMonHom_reducedClosedOriginalKernelGrp (A.X ⊗ B.X) Z (differenceHom A B F) hker
  exact ZInQ.Contrib.CloudB3W17bGraphScout.exists_scheme_realization_of_concrete_algebraic_graph
    A B F (reducedClosedOver (A.X ⊗ B.X) Z) (reducedClosedι (A.X ⊗ B.X) Z)
    (original_kernel_graph_iff A B F Z hker)

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
