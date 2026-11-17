/-
H5 lane3 Step 1: E3 = GM3, decomposition and assembly, with a SMOOTHNESS-FREE output (lead
economy audit, 2026-11-17). New file. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic.

AUDIT. No downstream consumer of `Y` uses smoothness. Only `IsAbelianVariety.proper` and
`IsAbelianVariety.geomIntegral` are read on `Y`:
* R3 / `TrivialOfSectionsBothWays`: proper and integral with a rational point;
* I5b on `Y`: C2's InversionFromSeesaw reads only `.proper` and `.geomIntegral` (lines 39–40);
* GM1 on `Y × Y` and on `H̄ × Y`: proper and geometrically integral on the `X` side, locally of
  finite type and reduced on the `T` side;
* G6: `FBSUnitFinite` (C4) uses `appTop_bijective_of_isAbelianVariety`, i.e. proper and integral;
  `FBSNonzeroSection` needs `Nonempty`;
* T and SS: the group object and `IsMonHom j`;
* the shear (ShearVanishing): `CompactSpace` and `Nonempty`, from proper and the rational point.
Smoothness is used ONLY for `H̄` itself (I1BaseChange). So E3's output class is
`IsProperIntegralGroup` (proper + geometrically integral). The consumer Props on `Y` move to this
class in Interfaces v2, agreed with C2 (I5b) and C4 (FBSUnitFinite); their proofs are unchanged.

v2 (interface v2; v1 7de68a8d is in history/): the class and its instance moved to
ProperIntegralGroup.lean, and the E3 Prop `InfiniteClosedSubgroupContainsIntegral` moved to
Extraction.lean v2.

PROVED here, modulo compile:
* `isProper_of_closedImmersion`: a closed subgroup of a proper group is proper;
* `infiniteClosedSubgroupContainsIntegral (hA hB hC)`: the E3 assembly.

Explicit UNPROVED sub-gaps, classical (lead's route), with NO smoothness:
* E3a `ReducedClosedSubgroup`: the reduced induced closed subscheme on `Z` is a closed subgroup
  object whose rational points are exactly `S`.
  - Mathlib `IdealSheafData.vanishingIdeal` gives the reduced structure.
  - `μ ∘ (ι × ι)` and `ι ∘ inv` land in `Z` set-theoretically, by density of rational points of
    the Jacobson scheme `Z ×_K Z` (`SeesawDensity`-type argument).
  - They factor through the reduced subscheme because `Z ×_K Z` is reduced over the algebraically
    closed `K`.
  - The group axioms hold because `ι` is a monomorphism.
* E3b `IdentityComponentIntegral`: a reduced closed subgroup with infinitely many rational points
  contains a geometrically integral closed subgroup `Y` with infinitely many rational points.
  - `Y` is the irreducible component through `e`. It is a subgroup: the product of irreducibles
    over `K` is irreducible (cf. the RECEIVED H71 Cube4 `geometricallyIntegral_fst_comp` 995a4a19,
    lower import unread), and the product of all components through `e` is a component through
    `e`, so there is only one.
  - There are finitely many components (Noetherian), and they are translates of `Y`, so `Y` has
    infinitely many points.
* E3c `NotFiniteOfInfinitePoints`: a scheme finite over `Spec K` has finitely many `K`-points.
  Finitely many points, and Mathlib `ext_of_apply_closedPoint_eq` makes `K`-points injective in
  points.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Extraction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- A closed subgroup of a proper group is proper. -/
theorem isProper_of_closedImmersion {K : Type u} [Field K]
    {A Y : Grp (Over (Spec (CommRingCat.of K)))} [IsProper A.X.hom] (j : Y.X ⟶ A.X)
    [IsClosedImmersion j.left] : IsProper Y.X.hom := by
  rw [← Over.w j]
  infer_instance

/-- E3a (UNPROVED): the reduced closed subgroup with rational points `S`. -/
def ReducedClosedSubgroup : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (Z : Set A.X.left), IsClosed Z →
    ∀ (S : Set (Pt K ⟶ A.X)), (∀ x, x ∈ S ↔ x.left.base (IsLocalRing.closedPoint K) ∈ Z) →
      (1 : Pt K ⟶ A.X) ∈ S → (∀ x y, x ∈ S → y ∈ S → x * y ∈ S) → (∀ x, x ∈ S → x⁻¹ ∈ S) →
        ∃ (G : Grp (Over (Spec (CommRingCat.of K)))) (ι : G.X ⟶ A.X) (_ : IsMonHom ι),
          IsClosedImmersion ι.left ∧ IsReduced G.X.left ∧
            (∀ g : Pt K ⟶ G.X, g ≫ ι ∈ S) ∧ (∀ x ∈ S, ∃ g : Pt K ⟶ G.X, g ≫ ι = x)

/-- E3b (UNPROVED): the identity component is a geometrically integral closed subgroup. -/
def IdentityComponentIntegral : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
    [IsProper G.X.hom] [IsReduced G.X.left], (Set.univ : Set (Pt K ⟶ G.X)).Infinite →
      ∃ (Y : Grp (Over (Spec (CommRingCat.of K)))) (j : Y.X ⟶ G.X) (_ : IsMonHom j),
        IsClosedImmersion j.left ∧ GeometricallyIntegral Y.X.hom ∧
          (Set.univ : Set (Pt K ⟶ Y.X)).Infinite

/-- E3c (UNPROVED, Mathlib-level): finitely many rational points of a finite scheme. -/
def NotFiniteOfInfinitePoints : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (Y : Grp (Over (Spec (CommRingCat.of K)))),
    (Set.univ : Set (Pt K ⟶ Y.X)).Infinite → ¬ IsFinite Y.X.hom

/-- E3 assembly, PROVED from E3a, E3b, E3c. -/
theorem infiniteClosedSubgroupContainsIntegral (hA : ReducedClosedSubgroup.{u})
    (hB : IdentityComponentIntegral.{u}) (hC : NotFiniteOfInfinitePoints.{u}) :
    InfiniteClosedSubgroupContainsIntegral.{u} := by
  intro K _ _ A _ Z hZ S hS h1 hmul hinv hinf
  obtain ⟨G, ι, hι, hιc, hGred, hGS, hSG⟩ := hA A Z hZ S hS h1 hmul hinv
  haveI := hι
  haveI := hιc
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : IsProper G.X.hom := isProper_of_closedImmersion ι
  -- `G` has infinitely many rational points: they surject onto the infinite `S`
  have hGinf : (Set.univ : Set (Pt K ⟶ G.X)).Infinite := by
    intro hfin
    apply hinf
    refine (hfin.image (fun g => g ≫ ι)).subset ?_
    intro x hx
    obtain ⟨g, rfl⟩ := hSG x hx
    exact ⟨g, Set.mem_univ _, rfl⟩
  obtain ⟨Y, j, hj, hjc, hYgi, hYinf⟩ := hB G hGinf
  haveI := hj
  haveI := hjc
  haveI : IsProper Y.X.hom := isProper_of_closedImmersion j
  refine ⟨Y, ⟨inferInstance, hYgi⟩, j ≫ ι, inferInstance, ?_, hC Y hYinf, fun y => ?_⟩
  · change IsClosedImmersion (j.left ≫ ι.left)
    infer_instance
  · rw [← Category.assoc]
    exact hGS (y ≫ j)

end ZInQ.Contrib.CloudR2NOS.Step1
