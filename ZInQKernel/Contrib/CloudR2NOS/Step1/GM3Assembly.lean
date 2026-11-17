/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/GM3Assembly.lean (sha256 cd248cffd92d1df24796e0ed85786a53da01c127f5da54562607825168a55804).
Body change relative to the base: ONLY P5, the line `open CategoryTheory.CartesianMonoidalCategory` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: E3a and E3b PROVED from the refined obligations of GM3Plan.lean. 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic, no smoothness.

PROVED here, modulo compile:
* `reducedClosedSubgroup : ClosedUnderOpsOfPoints → ReducedSubgroupOfClosedSubset →
  ReducedClosedSubgroup`, i.e. E3a.
* `identityComponentIntegral`, i.e. E3b, from `TranslateComponent`,
  `IdentityComponentClosedUnderOps`, the constructor, `IrreducibleSpaceOfClosedImmersionRange`,
  and the two EGA facts (GM3Plan). The steps are:
  - the pigeonhole (GM3Plan, proved);
  - translate the component to the identity;
  - closure under the group operations;
  - the reduced closed subgroup;
  - irreducible + reduced ⇒ integral, then geometrically integral over algebraically closed `K`;
  - infinitely many points via lifting.
* `infiniteClosedSubgroupContainsIntegral_full`: E3 from all of these and E3c (GM3Points, proved).

Obligations, each TRUE. Their exact statements are below and were added to TRUTH_LEDGER:
* `ReducedSubgroupOfClosedSubset` (constructor): the reduced induced closed subscheme on a closed
  set that is closed under the group operations is a closed subgroup object. Its range is the set,
  and rational points of the set lift (`Spec K` is reduced).
* `ClosedUnderOpsOfPoints`: closure of a closed set under the operations, from its rational
  points (Jacobson).
* `IdentityComponentClosedUnderOps`: the component through `e` of a reduced proper group is closed
  under the operations.
* `TranslateComponent`: translating a component with infinitely many rational points to one
  through `e`.
* `IrreducibleSpaceOfClosedImmersionRange`: a closed immersion with irreducible range has an
  irreducible source (closed embedding).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Plan
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Points

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- Constructor (TRUE): the reduced closed subgroup on a closed set closed under the operations. -/
def ReducedSubgroupOfClosedSubset : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [IsProper A.X.hom] (Z : Set A.X.left), IsClosed Z →
    (η[A.X] : Pt K ⟶ A.X).left.base (IsLocalRing.closedPoint K) ∈ Z →
    (∀ p : (A.X ⊗ A.X).left, (fst A.X A.X).left.base p ∈ Z → (snd A.X A.X).left.base p ∈ Z →
      μ[A.X].left.base p ∈ Z) →
    (∀ a ∈ Z, ι[A.X].left.base a ∈ Z) →
      ∃ (G : Grp (Over (Spec (CommRingCat.of K)))) (j : G.X ⟶ A.X) (_ : IsMonHom j),
        IsClosedImmersion j.left ∧ IsReduced G.X.left ∧ Set.range j.left.base = Z ∧
          ∀ x : Pt K ⟶ A.X, x.left.base (IsLocalRing.closedPoint K) ∈ Z →
            ∃ g : Pt K ⟶ G.X, g ≫ j = x

/-- (TRUE; Jacobson) A closed set whose rational points form a subgroup is closed under the
operations. -/
def ClosedUnderOpsOfPoints : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [IsProper A.X.hom] (Z : Set A.X.left), IsClosed Z →
    ∀ (S : Set (Pt K ⟶ A.X)), (∀ x, x ∈ S ↔ x.left.base (IsLocalRing.closedPoint K) ∈ Z) →
      (1 : Pt K ⟶ A.X) ∈ S → (∀ x y, x ∈ S → y ∈ S → x * y ∈ S) → (∀ x, x ∈ S → x⁻¹ ∈ S) →
        (η[A.X] : Pt K ⟶ A.X).left.base (IsLocalRing.closedPoint K) ∈ Z ∧
        (∀ p : (A.X ⊗ A.X).left, (fst A.X A.X).left.base p ∈ Z → (snd A.X A.X).left.base p ∈ Z →
          μ[A.X].left.base p ∈ Z) ∧
        (∀ a ∈ Z, ι[A.X].left.base a ∈ Z)

/-- (TRUE) The component through `e` of a reduced proper group is closed under the operations. -/
def IdentityComponentClosedUnderOps : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
    [IsProper G.X.hom] [IsReduced G.X.left], ∀ C ∈ irreducibleComponents G.X.left,
    (η[G.X] : Pt K ⟶ G.X).left.base (IsLocalRing.closedPoint K) ∈ C →
      (∀ p : (G.X ⊗ G.X).left, (fst G.X G.X).left.base p ∈ C → (snd G.X G.X).left.base p ∈ C →
        μ[G.X].left.base p ∈ C) ∧ (∀ a ∈ C, ι[G.X].left.base a ∈ C)

/-- (TRUE) Translating a component with infinitely many rational points to the identity. -/
def TranslateComponent : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
    [IsProper G.X.hom], ∀ C ∈ irreducibleComponents G.X.left,
    ((fun g : Pt K ⟶ G.X => g.left.base (IsLocalRing.closedPoint K)) ⁻¹' C).Infinite →
      ∃ C' ∈ irreducibleComponents G.X.left,
        (η[G.X] : Pt K ⟶ G.X).left.base (IsLocalRing.closedPoint K) ∈ C' ∧
          ((fun g : Pt K ⟶ G.X => g.left.base (IsLocalRing.closedPoint K)) ⁻¹' C').Infinite

/-- (TRUE) A closed immersion with irreducible range has an irreducible source. -/
def IrreducibleSpaceOfClosedImmersionRange : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f], IsIrreducible (Set.range f.base) →
    IrreducibleSpace X

/-- E3a, PROVED from the constructor and `ClosedUnderOpsOfPoints`. -/
theorem reducedClosedSubgroup (hCO : ClosedUnderOpsOfPoints.{u})
    (hK : ReducedSubgroupOfClosedSubset.{u}) : ReducedClosedSubgroup.{u} := by
  intro K _ _ A _ Z hZ S hS h1 hmul hinv
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  obtain ⟨he, hm, hi⟩ := hCO A Z hZ S hS h1 hmul hinv
  obtain ⟨G, ι', hι, hιc, hGred, hrange, hlift⟩ := hK A Z hZ he hm hi
  refine ⟨G, ι', hι, hιc, hGred, fun g => ?_, fun x hx => hlift x ((hS x).mp hx)⟩
  rw [hS, ← hrange]
  exact ⟨g.left.base (IsLocalRing.closedPoint K), rfl⟩

/-- E3b, PROVED from the refined obligations. -/
theorem identityComponentIntegral (hT : TranslateComponent.{u})
    (hC : IdentityComponentClosedUnderOps.{u}) (hK : ReducedSubgroupOfClosedSubset.{u})
    (hIrr : IrreducibleSpaceOfClosedImmersionRange.{u}) (hR : GeomReducedOverAlgClosed.{u})
    (hI : GeomIrreducibleOverAlgClosed.{u}) : IdentityComponentIntegral.{u} := by
  intro K _ _ G _ _ hinf
  haveI : NoetherianSpace G.X.left := inferInstance
  obtain ⟨C, hC0, hCinf⟩ := exists_irreducibleComponent_infinite_preimage
    (fun g : Pt K ⟶ G.X => g.left.base (IsLocalRing.closedPoint K)) hinf
  obtain ⟨C', hC', he, hC'inf⟩ := hT G C hC0 hCinf
  obtain ⟨hmul, hinv⟩ := hC G C' hC' he
  obtain ⟨Y, j, hj, hjc, hYred, hrange, hlift⟩ :=
    hK G C' (isClosed_of_mem_irreducibleComponents C' hC') he hmul hinv
  haveI := hj
  haveI := hjc
  haveI := hYred
  haveI : IrreducibleSpace Y.X.left := hIrr j.left (by rw [hrange]; exact hC'.1)
  haveI : IsIntegral Y.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : LocallyOfFiniteType Y.X.hom := by
    rw [← Over.w j]
    infer_instance
  refine ⟨Y, j, hj, hjc, geometricallyIntegral_of_isIntegral hR hI Y.X.hom, ?_⟩
  intro hfin
  apply hC'inf
  refine (hfin.image (fun y => y ≫ j)).subset ?_
  intro x hx
  obtain ⟨g, hg⟩ := hlift x hx
  exact ⟨g, Set.mem_univ _, hg⟩

/-- E3 in full, from the refined obligations and E3c (proved). -/
theorem infiniteClosedSubgroupContainsIntegral_full (hCO : ClosedUnderOpsOfPoints.{u})
    (hK : ReducedSubgroupOfClosedSubset.{u}) (hT : TranslateComponent.{u})
    (hC : IdentityComponentClosedUnderOps.{u})
    (hIrr : IrreducibleSpaceOfClosedImmersionRange.{u}) (hR : GeomReducedOverAlgClosed.{u})
    (hI : GeomIrreducibleOverAlgClosed.{u}) : InfiniteClosedSubgroupContainsIntegral.{u} :=
  infiniteClosedSubgroupContainsIntegral_of (reducedClosedSubgroup hCO hK)
    (identityComponentIntegral hT hC hK hIrr hR hI)

end ZInQ.Contrib.CloudR2NOS.Step1
