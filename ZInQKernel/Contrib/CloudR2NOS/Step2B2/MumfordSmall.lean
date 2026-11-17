/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B2/MumfordSmall.lean (sha256 736ecc0ac1403a61ef7e6ae46562585f4637a899bccf09566ccf9dc72397b6f2).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B2.d (d.3): `MumfordContractedCombinatorics` PROVED from (d.1)
`MinkowskiIrreducible` (lane3, open), (d.2) `PurityTranslateEquality` (C5), Mathlib
commutativity, and FIVE small TRUE point/topology obligations. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Small obligations (TRUE):
* `PointTranslation`: `t_y(pt x) = pt (x * y)`. Composition of terminal points with
  `lift 𝟙 (toUnit ≫ y) ≫ μ`.
* `PointInversion`: `ι(pt x) = pt x⁻¹` (`Hom.inv_def`).
* `RationalPointsDetermineClosed`: if every rational point of a closed `E` lies in a closed `Z`,
  then `E ⊆ Z`. Rational points are the closed points (`pointEquivClosedPoint`), and closed points
  are dense in closed subsets (Jacobson).
* `IrreducibleInComponent`: an irreducible subset of `supp D` lies in a maximal one (Noetherian;
  Mathlib `exists_mem_irreducibleComponents_subset_of_isIrreducible` on the subspace).
* `PointsOfSupportInComponents`: every point of `supp D` lies in some component (the previous
  item applied to the closure of a singleton).
`SupportComponentsFinite` (B1, C4) supplies finiteness of the components.

Proof: commutativity (`IsCommMonObj` for `A.X`) makes the rational points a commutative group.
Write `pt x := x.left(closedPoint)`. Fix `c₀ ∈ C(K)`.
1. Every component `F` is fixed by `t_{c·c₀⁻¹}` for each `c ∈ C(K)`.
   - The Minkowski set `F(K)·C(K)⁻¹` lies in `Q ∪ ι⁻¹Q`. Its closure is irreducible by (d.1),
     so case A or case B.
   - Each case uses the component trick, then (d.2).
2. Therefore `t_{c c₀⁻¹}⁻¹ Z = Z`, and `c ↦ c c₀⁻¹` is injective on the infinite `C(K)`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MumfordPlan
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.Assembly
import Mathlib.AlgebraicGeometry.Group.Abelian

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation
local notation "Pt" K => 𝟙_ (Over (Spec (CommRingCat.of K)))

/-- (TRUE) Right translation on rational points. -/
def PointTranslation : Prop :=
  ∀ {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K)))) (x y : (Pt K) ⟶ A.X),
    (tr A y) (x.left (IsLocalRing.closedPoint K)) = (x * y).left (IsLocalRing.closedPoint K)

/-- (TRUE) Inversion on rational points. -/
def PointInversion : Prop :=
  ∀ {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K)))) (x : (Pt K) ⟶ A.X),
    (ι[A.X]).left (x.left (IsLocalRing.closedPoint K)) = (x⁻¹).left (IsLocalRing.closedPoint K)

/-- (TRUE; Jacobson) Rational points determine inclusions of closed sets. -/
def RationalPointsDetermineClosed : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (E Z : Set A.X.left), IsClosed E → IsClosed Z →
    (∀ x : (Pt K) ⟶ A.X, x.left (IsLocalRing.closedPoint K) ∈ E →
      x.left (IsLocalRing.closedPoint K) ∈ Z) → E ⊆ Z

/-- (TRUE; Noetherian) An irreducible subset of the support lies in a maximal one. -/
def IrreducibleInComponent : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (D : A.X.left.IdealSheafData) (E : Set A.X.left),
    E ⊆ (D.support : Set A.X.left) → IsIrreducible E →
      ∃ G, Maximal (fun Y : Set A.X.left => Y ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Y) G ∧
        E ⊆ G

/-- (TRUE) Every point of the support lies in a component. -/
def PointsOfSupportInComponents : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (D : A.X.left.IdealSheafData) (z : A.X.left),
    z ∈ (D.support : Set A.X.left) →
      ∃ G, Maximal (fun Y : Set A.X.left => Y ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Y) G ∧
        z ∈ G

end ZInQ.Contrib.CloudR2NOS.Step2B2
