/-
H5 lane3 Step 1: E3a/E3b refined into Mathlib-level obligations, plus the component pigeonhole
PROVED. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

E3a `ReducedClosedSubgroup` and E3b `IdentityComponentIntegral` (GM3.lean v2) both factor through
ONE constructor and a few classical facts. The Props below are stated so that they can be worked
in PARALLEL. Each is TRUE; none is used as a final premise.
* `GeomReducedOverAlgClosed` (true; EGA IV 4.6.1): over an algebraically closed field, a reduced
  scheme locally of finite type is geometrically reduced. Mathlib has only the base-change
  stability (Geometrically/Reduced.lean) and `isReduced` of products for geometrically reduced,
  flat, locally Noetherian factors.
* `GeomIrreducibleOverAlgClosed` (true; EGA IV 4.5.8): over an algebraically closed field, an
  irreducible scheme locally of finite type is geometrically irreducible.
* `ReducedSubgroupOfClosedSubset` (the constructor): if a closed `Z ∋ e` is closed under `μ` (on
  `pr₁⁻¹Z ∩ pr₂⁻¹Z ⊆ |A ×_K A|`) and under `ι`, then the reduced induced closed subscheme
  (Mathlib `IdealSheafData.vanishingIdeal`) is a closed subgroup object with range `Z`.
  - `μ` and `ι` factor because `Z_red ×_K Z_red` is reduced (`GeomReducedOverAlgClosed` plus the
    Mathlib product instance).
  - The group axioms descend along the monomorphism `ι_Z`.
* `ClosedUnderOpsOfPoints` (true; Jacobson): if a closed `Z` has rational points forming a
  subgroup, then `Z` is closed under `μ` and `ι` as above. The relevant subset of the product is
  closed and contains all closed points of the Jacobson scheme `Z_red ×_K Z_red`.
* `IdentityComponentClosedUnderOps` (true): for a reduced proper group, the irreducible component
  `C` through `e` is closed under `μ` and `ι`.
  - `μ(C × C)` is irreducible (`GeomIrreducibleOverAlgClosed` plus Mathlib's irreducible products)
    and contains `C` via `(c, e)`, so it lies in `C` by maximality.
  - `ι(C)` is a component through `e`, and `μ(C × ι C)` contains both, so `ι C = C`.
* `TranslateComponent` (true): right translation by a rational point is a homeomorphism. It
  permutes the irreducible components and acts bijectively on rational points, so a component
  with infinitely many rational points translates to one through `e` with the same property.
PROVED here: `exists_irreducibleComponent_infinite_preimage` (Mathlib topology). In a Noetherian
space, infinitely many points (via any map) give a component containing infinitely many of them.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- Pigeonhole over irreducible components, PROVED. -/
theorem exists_irreducibleComponent_infinite_preimage {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {ι : Type*} (p : ι → X) (hinf : (Set.univ : Set ι).Infinite) :
    ∃ C ∈ irreducibleComponents X, (p ⁻¹' C).Infinite := by
  by_contra h
  apply hinf
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcover : (Set.univ : Set ι) ⊆ ⋃ C ∈ irreducibleComponents X, p ⁻¹' C := by
    intro i _
    obtain ⟨C, hC, hpC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {p i} isIrreducible_singleton
    exact Set.mem_biUnion hC (hpC rfl)
  refine (hfin.biUnion fun C hC => ?_).subset hcover
  by_contra hC'
  exact h ⟨C, hC, hC'⟩

/-- Obligation (TRUE; EGA IV 4.6.1): reduced ⇒ geometrically reduced over an algebraically
closed field. -/
def GeomReducedOverAlgClosed : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [IsReduced X], GeometricallyReduced f

/-- Obligation (TRUE; EGA IV 4.5.8): irreducible ⇒ geometrically irreducible over an
algebraically closed field. -/
def GeomIrreducibleOverAlgClosed : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [IrreducibleSpace X], GeometricallyIrreducible f

/-- Integral ⇒ geometrically integral over an algebraically closed field, from the two
obligations. PROVED. -/
theorem geometricallyIntegral_of_isIntegral (hR : GeomReducedOverAlgClosed.{u})
    (hI : GeomIrreducibleOverAlgClosed.{u}) {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [IsIntegral X] :
    GeometricallyIntegral f := by
  haveI := hR f
  haveI := hI f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end ZInQ.Contrib.CloudR2NOS.Step1
