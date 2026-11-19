/-
H5 lane3 Step 1: E3c `NotFiniteOfInfinitePoints` (GM3.lean) PROVED from Mathlib. 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED. Universe u.

The proof:
* If `Y → Spec K` were finite, its points over the unique point of `Spec K` would form a finite set
  (Mathlib `Scheme.Hom.finite_preimage_singleton`, finite ⇒ locally quasi-finite and
  quasi-compact).
* The map from `K`-points to points is injective (Mathlib `ext_of_apply_closedPoint_eq`, `K`
  algebraically closed and finite ⇒ locally of finite type).
* Hence there would be finitely many `K`-points.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem notFiniteOfInfinitePoints : NotFiniteOfInfinitePoints.{u} := by
  intro K _ _ Y hinf hfin
  apply hinf
  have hinj : Set.InjOn (fun y : Pt K ⟶ Y.X => y.left (IsLocalRing.closedPoint K)) Set.univ := by
    intro y _ y' _ h
    exact Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq Y.X.hom (Over.w y) (Over.w y') h)
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Y.X.hom.finite_preimage_singleton (IsLocalRing.closedPoint K)).subset ?_
  rintro _ ⟨y, -, rfl⟩
  exact Subsingleton.elim _ _

/-- E3 (smoothness-free) with E3c discharged: from E3a and E3b. -/
theorem infiniteClosedSubgroupContainsIntegral_of (hA : ReducedClosedSubgroup.{u})
    (hB : IdentityComponentIntegral.{u}) : InfiniteClosedSubgroupContainsIntegral.{u} :=
  infiniteClosedSubgroupContainsIntegral hA hB notFiniteOfInfinitePoints

end ZInQ.Contrib.CloudR2NOS.Step1
