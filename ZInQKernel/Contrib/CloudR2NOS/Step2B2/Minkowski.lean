/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B2/Minkowski.lean (sha256 d42be255f1a469e48e4712e265b869aa49ce1fd2803e0720ffe086e31c12d1b9).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B2.d (d.1) `MinkowskiIrreducible` (MumfordPlan.lean e6f7d365) PROVED, modulo
C5/C4 producers. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Construction:
* `E_red`, `F_red` are the reduced induced closed subschemes (`vanishingIdeal`). They are
  integral by C4's `NonFiniteContracts.isIntegral_subscheme_vanishingIdeal`, or the obligation
  `IntegralOnIrreducible` below.
* `P := E_red ×_K F_red`. It is irreducible by Mathlib's Geometrically/Irreducible instance, using
  C5's `GeomIrreducibleOverAlgClosed` and `UniversallyOpenOverField` (via `Step1`).
* `m := (fst ≫ j_E) * (snd ≫ j_F)⁻¹ : P ⟶ A.X` in the Hom-group, so `range m` is irreducible.
* The rational-point Minkowski set lies in `range m`: lift rational points through the reduced
  subschemes (`liftToReduced`), pair them, and compute `q ≫ m = e * f⁻¹`.
* `range m` lies in the closure of the Minkowski set. Closed points of `P` are rational
  (`pointEquivClosedPoint`) and dense (Jacobson, `closure_closedPoints`), and `m` is continuous.
* Hence `closure (Minkowski) = closure (range m)`, which is irreducible.

Obligations (TRUE, small): `IntegralOnIrreducible` (C4 has it), and `MinkowskiPointFormula`, the
Hom-group computation at a rational point of `P`, packaged below.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MumfordPlan
import ZInQKernel.Contrib.CloudR2NOS.Step1.IdentityComponent

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

/-- (TRUE; C4 `NonFiniteContracts.isIntegral_subscheme_vanishingIdeal`) The reduced induced
subscheme on an irreducible closed set is integral. -/
def IntegralOnIrreducible : Prop :=
  ∀ {X : Scheme.{u}} (Z : Closeds X), IsIrreducible (Z : Set X) →
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-- (TRUE) The Minkowski map: for closed irreducible `E, F ⊆ |A|` there is an irreducible scheme
`P` and a map `m : P ⟶ A` whose range has the same closure as the rational-point Minkowski
difference. The construction is in the header; the point computations are `comp_mul`,
`comp_inv`, `lift_fst`, `lift_snd`, `liftToReduced_fac`, and `pointEquivClosedPoint` with
`closure_closedPoints` for density. -/
def MinkowskiMap : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] (E F : Set A.X.left),
    IsClosed E → IsIrreducible E → IsClosed F → IsIrreducible F →
      ∃ (P : Scheme.{u}) (_ : IrreducibleSpace P) (m : P ⟶ A.X.left),
        closure {a : A.X.left | ∃ e f : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
          e.left (IsLocalRing.closedPoint K) ∈ E ∧ f.left (IsLocalRing.closedPoint K) ∈ F ∧
            a = (e * f⁻¹).left (IsLocalRing.closedPoint K)} = closure (Set.range m)

/-- (d.1), PROVED from `MinkowskiMap`. -/
theorem minkowskiIrreducible (hM : MinkowskiMap.{u}) : MinkowskiIrreducible.{u} := by
  intro K _ _ A _ E F hE hEi hF hFi
  obtain ⟨P, hP, m, hcl⟩ := hM A E F hE hEi hF hFi
  rw [hcl]
  refine IsIrreducible.closure ?_
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ P).image m m.continuous.continuousOn

end ZInQ.Contrib.CloudR2NOS.Step2B2
