/-
Lane5 producer of the exact C3 ClosedUnderOpsOfPoints.{u}.
SOURCE ONLY / UNCOMPILED. Truth pre-check: true under the actual proper/LFT
and algebraically-closed field hypotheses. This is ONLY set-theoretic closure
under the group operations. It does not infer equality of ideals, a subgroup
scheme structure, or any multiplicity from equality of supports.

A closed subset of a Jacobson scheme is the closure of its closed points.
Every closed point over the algebraically closed field is rational. Apply
that fact to the product's closed subset defined by both projections lying
in Z; rational product points decompose into the two rational projections.
The inverse assertion uses the same closed-point argument on Z. No smoothness,
reducedness, characteristic or dimension restriction is added.
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Assembly

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace H5OriginalDVR.Lane5.GM3Points

/-- Closed-point density on a closed subset; no ideal-factorisation claim. -/
theorem subset_of_closedPoint_subset
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (T Q : Set X) (hT : IsClosed T) (hQ : IsClosed Q)
    (h : ∀ x ∈ T, IsClosed {x} → x ∈ Q) : T ⊆ Q := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hd : closure (T ∩ closedPoints X) = T :=
    (JacobsonSpace.closure_inter_closedPoints_eq_closure hT.isLocallyClosed).trans hT.closure_eq
  rw [← hd]
  exact closure_minimal (fun x hx => h x hx.1 hx.2) hQ

/-- EXACT consumer: rational subgroup points force the closed SET to be
closed under the actual scheme group operations on all scheme points. -/
theorem closedUnderOpsOfPoints :
    ZInQ.Contrib.CloudR2NOS.Step1.ClosedUnderOpsOfPoints.{u} := by
  intro k _ _ A _ Z hZ S hS h1 hmul hinv
  letI : LocallyOfFiniteType A.X.hom := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · change (1 : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ A.X).left.base
      (IsLocalRing.closedPoint k) ∈ Z
    exact (hS 1).mp h1
  · let P := A.X ⊗ A.X
    let p1 : P ⟶ A.X := fst A.X A.X
    let p2 : P ⟶ A.X := snd A.X A.X
    letI : LocallyOfFiniteType P.hom := by
      change LocallyOfFiniteType (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
      infer_instance
    let T : Set P.left := p1.left.base ⁻¹' Z ∩ p2.left.base ⁻¹' Z
    let Q : Set P.left := μ[A.X].left.base ⁻¹' Z
    have hT : IsClosed T :=
      (hZ.preimage p1.left.continuous).inter (hZ.preimage p2.left.continuous)
    have hQ : IsClosed Q := hZ.preimage μ[A.X].left.continuous
    have hclosed : ∀ p ∈ T, IsClosed {p} → p ∈ Q := by
      intro p hp hpClosed
      let e := pointOfClosedPoint P.hom p hpClosed
      let t : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ P :=
        Over.homMk e (pointOfClosedPoint_comp P.hom p hpClosed)
      let x := t ≫ p1
      let y := t ≫ p2
      have hxPoint : x.left.base (IsLocalRing.closedPoint k) = p1.left.base p := by
        simp only [x, t, e, Over.comp_left, Over.homMk_left,
          Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
      have hyPoint : y.left.base (IsLocalRing.closedPoint k) = p2.left.base p := by
        simp only [y, t, e, Over.comp_left, Over.homMk_left,
          Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
      have hxS : x ∈ S := (hS x).mpr (hxPoint.symm ▸ hp.1)
      have hyS : y ∈ S := (hS y).mpr (hyPoint.symm ▸ hp.2)
      have ht : t ≫ μ[A.X] = x * y := by
        change t ≫ μ[A.X] = lift x y ≫ μ[A.X]
        congr 1
        apply CartesianMonoidalCategory.hom_ext <;> simp only [x, y, lift_fst, lift_snd]
      have hxyPoint : (x * y).left.base (IsLocalRing.closedPoint k) = μ[A.X].left.base p := by
        rw [← ht]
        simp only [t, e, Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply,
          pointOfClosedPoint_apply]
      exact hxyPoint ▸ (hS (x * y)).mp (hmul x y hxS hyS)
    have hsub : T ⊆ Q := subset_of_closedPoint_subset P.hom T Q hT hQ hclosed
    intro p hp1 hp2
    exact hsub ⟨hp1, hp2⟩
  · let Q : Set A.X.left := ι[A.X].left.base ⁻¹' Z
    have hQ : IsClosed Q := hZ.preimage ι[A.X].left.continuous
    have hclosed : ∀ a ∈ Z, IsClosed {a} → a ∈ Q := by
      intro a ha haClosed
      let e := pointOfClosedPoint A.X.hom a haClosed
      let x : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ A.X :=
        Over.homMk e (pointOfClosedPoint_comp A.X.hom a haClosed)
      have hxPoint : x.left.base (IsLocalRing.closedPoint k) = a := by
        simp only [x, e, Over.homMk_left, pointOfClosedPoint_apply]
      have hxS : x ∈ S := (hS x).mpr (hxPoint.symm ▸ ha)
      have hiPoint : (x⁻¹).left.base (IsLocalRing.closedPoint k) = ι[A.X].left.base a := by
        change (x.left ≫ ι[A.X].left).base (IsLocalRing.closedPoint k) = _
        simp only [Scheme.Hom.comp_apply, hxPoint]
      exact hiPoint ▸ (hS (x⁻¹)).mp (hinv x hxS)
    exact subset_of_closedPoint_subset A.X.hom Z Q hZ hQ hclosed

end H5OriginalDVR.Lane5.GM3Points
