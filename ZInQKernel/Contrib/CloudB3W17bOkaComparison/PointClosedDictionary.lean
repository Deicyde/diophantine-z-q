import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Native complex points and actual closed scheme points

This is an original comparison for the unchanged complex-point carrier.  The
closed-point dictionary uses Mathlib's proved Nullstellensatz consequence, not
an algebraicity witness or a supplied compatibility structure.  It deliberately
makes no assertion that a point bijection is a morphism of ringed spaces.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The native over-category point is a section of the genuine structure morphism. -/
def nativePointSectionEquiv (X : Over (Spec (CommRingCat.of ℂ))) :
    ComplexPoint X ≃ {p : Spec (CommRingCat.of ℂ) ⟶ X.left // p ≫ X.hom = 𝟙 _} where
  toFun p := ⟨p.left, by simpa using Over.w p⟩
  invFun p := Over.homMk p.1 (by simpa using p.2)
  left_inv p := by
    apply Over.OverMorphism.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Genuine native complex points are precisely closed points of an LFT complex scheme. -/
def nativePointClosedEquiv (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] : ComplexPoint X ≃ closedPoints X.left :=
  (nativePointSectionEquiv X).trans (pointEquivClosedPoint X.hom)

@[simp]
theorem nativePointClosedEquiv_val (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (p : ComplexPoint X) :
    (nativePointClosedEquiv X p).1 = p.underlying := rfl

/-- The closed-point dictionary is natural for actual scheme morphisms. -/
theorem nativePointClosedEquiv_map_val
    {X Y : Over (Spec (CommRingCat.of ℂ))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ComplexPoint X) :
    (nativePointClosedEquiv Y (Point.map f p)).1 =
      f.left (nativePointClosedEquiv X p).1 := rfl

/-- ORIGINAL complex-point morphisms have the same closed-point dictionary. -/
def originalPointClosedEquiv (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] : CloudB3W17Hodge.CPt X ≃ closedPoints X.left :=
  (CloudB3W17Hodge.cptEquiv X).trans (nativePointClosedEquiv X)

@[simp]
theorem originalPointClosedEquiv_val (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (p : CloudB3W17Hodge.CPt X) :
    (originalPointClosedEquiv X p).1 = p.left (IsLocalRing.closedPoint ℂ) := rfl

/-- No choice of a new point model is involved in the original-point Zariski domains. -/
theorem originalPointClosedEquiv_mem_open (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (p : CloudB3W17Hodge.CPt X) (U : X.left.Opens) :
    (originalPointClosedEquiv X p).1 ∈ U ↔ CloudB3W17Hodge.XPtIn X p U :=
  (CloudB3W17Hodge.ptIn_iff X p U).symm

/-- Original complex points are determined by their actual closed scheme point. -/
theorem originalPoint_ext_closed (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] {p q : CloudB3W17Hodge.CPt X}
    (h : p.left (IsLocalRing.closedPoint ℂ) = q.left (IsLocalRing.closedPoint ℂ)) : p = q :=
  (originalPointClosedEquiv X).injective (Subtype.ext h)

/-- The inverse closed-point dictionary preserves every regular-section evaluation. -/
theorem original_closed_eval (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] (x : closedPoints X.left)
    (U : X.left.Opens) (s : Γ(X.left, U)) :
    CloudB3W17Hodge.XevalAt X U s ((originalPointClosedEquiv X).symm x) =
      Point.evaluate U s ((nativePointClosedEquiv X).symm x) := by
  rw [CloudB3W17Hodge.xevalAt_eq_evaluate]
  congr 1

end ZInQ.Contrib.CloudB3W17bOkaComparison
