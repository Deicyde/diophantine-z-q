/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligations for C3's B2.d (`Step2B2/MumfordSmall.lean` 736ecc0a; statements used
verbatim through the import), PROVED natively. SOURCE ONLY, UNCOMPILED. Native HELD. Universe u,
default options.

* `pointTranslation`: `x ≫ (lift 𝟙 (toUnit ≫ y) ≫ μ) = lift x y ≫ μ = x * y` (`comp_lift`,
  `toUnit_unique`, Mathlib `Hom.mul_def`), then evaluate `.left` at the point.
* `pointInversion`: `x⁻¹ = x ≫ ι` (Mathlib `Hom.inv_def`).
* `rationalPointsDetermineClosed`: closed points of `E` are rational (Mathlib `pointOfClosedPoint`
  over the algebraically closed `K`), so `E ∩ closedPoints ⊆ Z`; `A` is Jacobson
  (`LocallyOfFiniteType.jacobsonSpace`), so `E = closure (E ∩ closedPoints) ⊆ Z`.
* `irreducibleInComponent`, `pointsOfSupportInComponents`: `Step2Small`'s Noetherian lemma on the
  closed `supp D` (and the irreducible singleton).
Truth: all TRUE (these are the proofs).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MumfordSmall
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.B1Small

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- **`PointTranslation` proved.** -/
theorem pointTranslation : ZInQ.Contrib.CloudR2NOS.Step2B2.PointTranslation.{u} := by
  intro K _ A x y
  have h : x ≫ (lift (𝟙 A.X) (toUnit A.X ≫ y) ≫ μ[A.X]) = x * y := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (x ≫ toUnit A.X) (𝟙 _), Category.id_comp]
  have h1 := congrArg (fun φ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X =>
    φ.left.base (IsLocalRing.closedPoint K)) h
  simp only [Over.comp_left, Scheme.Hom.comp_base, TopCat.comp_app] at h1
  exact h1

/-- **`PointInversion` proved.** -/
theorem pointInversion : ZInQ.Contrib.CloudR2NOS.Step2B2.PointInversion.{u} := by
  intro K _ A x
  rw [Hom.inv_def]
  rfl

/-- The rational point of `A` attached to a closed point. -/
noncomputable def ratPoint {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFiniteType A.X.hom] (c : A.X.left)
    (hc : IsClosed ({c} : Set A.X.left)) : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X :=
  Over.homMk (pointOfClosedPoint A.X.hom c hc) (pointOfClosedPoint_comp A.X.hom c hc)

theorem ratPoint_apply {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFiniteType A.X.hom] (c : A.X.left)
    (hc : IsClosed ({c} : Set A.X.left)) :
    (ratPoint A c hc).left (IsLocalRing.closedPoint K) = c :=
  pointOfClosedPoint_apply A.X.hom c hc _

/-- **`RationalPointsDetermineClosed` proved.** -/
theorem rationalPointsDetermineClosed :
    ZInQ.Contrib.CloudR2NOS.Step2B2.RationalPointsDetermineClosed.{u} := by
  intro K _ _ A _ E Z hE hZ h
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  have hcl : E ∩ closedPoints A.X.left ⊆ Z := by
    rintro c ⟨hcE, hc⟩
    have hx := ratPoint_apply A c hc
    have hmem := h (ratPoint A c hc) (by rw [hx]; exact hcE)
    rwa [hx] at hmem
  have hdense := JacobsonSpace.closure_inter_closedPoints_eq_closure hE.isLocallyClosed
  calc E = closure E := hE.closure_eq.symm
    _ = closure (E ∩ closedPoints A.X.left) := hdense.symm
    _ ⊆ Z := closure_minimal hcl hZ

/-- **`IrreducibleInComponent` proved.** -/
theorem irreducibleInComponent : ZInQ.Contrib.CloudR2NOS.Step2B2.IrreducibleInComponent.{u} := by
  intro K _ _ A _ D E hES hE
  haveI := noetherianSpace_abelianVariety A
  exact exists_maximal_irreducible_of_subset D.support.isClosed hES hE

/-- **`PointsOfSupportInComponents` proved.** -/
theorem pointsOfSupportInComponents :
    ZInQ.Contrib.CloudR2NOS.Step2B2.PointsOfSupportInComponents.{u} := by
  intro K _ _ A _ D z hz
  obtain ⟨G, hG, hzG⟩ := irreducibleInComponent A D {z} (Set.singleton_subset_iff.2 hz)
    isIrreducible_singleton
  exact ⟨G, hG, hzG (Set.mem_singleton z)⟩

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small
