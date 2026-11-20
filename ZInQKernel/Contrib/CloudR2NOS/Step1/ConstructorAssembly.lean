/-
H5 lane C3 STEP-F9 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane C3 STEP-F8 fix edition (2026-11-17), superseded by STEP-F9.
-/
/-
H5 lane C3 STEP-H1 public-hygiene edition (2026-11-17): comments only. The code is byte-identical to its base edition; only header and comment text changed.
-/
/-
H5 lane C3 STEP-F2 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane3 Step 1: the constructor `ReducedSubgroupOfClosedSubset` (GM3Assembly.lean) PROVED from
its obligations (ConstructorParts.lean) and C5's `GeomReducedOverAlgClosed`. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u, no smoothness.

Construction:
* `Z_red` is the reduced induced closed subscheme (`vanishingIdeal Z`), with `ι_Z` its closed
  immersion, made an object of `Over (Spec K)` via `ι_Z ≫ A.X.hom`.
* `e`, `m`, `i` are the lifts through `ι_Z` (`liftToReduced`) of `η`, `(ι_Z ⊗ ι_Z) ≫ μ` and
  `ι_Z ≫ ι`. Each range lies in `Z` by the closure hypotheses, and each source is reduced:
  - `Spec K` is reduced;
  - `Z_red` is reduced (`IsReducedSubschemeVanishingIdeal`);
  - `Z_red ×_K Z_red` is reduced: Mathlib's flat, locally Noetherian, geometrically reduced
    product instance, with `GeomReducedOverAlgClosed`.
* The group structure and `IsMonHom` come from `GrpObjOfCompatibleMono`.
* The range is `Z` (`range_subschemeι_vanishingIdeal`). Rational points of `Z` lift by
  `liftToReduced`, since `Spec K` is reduced.
Instance steps marked `inferInstance` rely on Mathlib's standard instances (closed immersion ⇒
mono, locally Noetherian, flat over a field). C6 or a compile run will confirm them.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.ConstructorParts

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem reducedSubgroupOfClosedSubset (hRed : IsReducedSubschemeVanishingIdeal.{u})
    (hGrp : GrpObjOfCompatibleMono.{u}) (hGR : GeomReducedOverAlgClosed.{u}) :
    ReducedSubgroupOfClosedSubset.{u} := by
  intro K _ _ A _ Z hZ he hmul hinv
  -- STEP-F8: instances at the `Over` forms that instance search meets (it does not unfold
  -- `𝟙_ (Over _)`, `Over.mk` or `Functor.fromPUnit`), each from its concrete form.
  haveI : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  haveI : Subsingleton (Pt K).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  haveI : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  haveI : IsReduced (Pt K).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  let Zc : Closeds A.X.left := ⟨Z, hZ⟩
  let ιZ := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme := hRed Zc
  have hrange : Set.range ιZ.base = Z := range_subschemeι_vanishingIdeal Zc
  have hmem : ∀ q, ιZ.base q ∈ Z := fun q => hrange ▸ ⟨q, rfl⟩
  let Zo : Over (Spec (CommRingCat.of K)) := Over.mk (ιZ ≫ A.X.hom)
  haveI : IsReduced Zo.left :=
    inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme)
  let jo : Zo ⟶ A.X := Over.homMk ιZ rfl
  haveI : Mono jo := Over.mono_of_mono_left jo
  -- the unit
  have h1 : Set.range (η[A.X] : Pt K ⟶ A.X).left.base ⊆ (Zc : Set A.X.left) := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact he
  let e : Pt K ⟶ Zo := Over.homMk (liftToReduced Zc _ h1) (by
    change liftToReduced Zc _ h1 ≫ ιZ ≫ A.X.hom = _
    rw [← Category.assoc, liftToReduced_fac]
    exact Over.w (η[A.X] : Pt K ⟶ A.X))
  have he' : e ≫ jo = η[A.X] := Over.OverMorphism.ext (liftToReduced_fac Zc _ h1)
  -- the multiplication
  haveI : LocallyOfFiniteType Zo.hom :=
    (inferInstance : LocallyOfFiniteType (show _ ⟶ Spec (CommRingCat.of K) from ιZ ≫ A.X.hom))
  haveI : Flat Zo.hom :=
    (inferInstance : Flat (show _ ⟶ Spec (CommRingCat.of K) from ιZ ≫ A.X.hom))
  haveI : IsLocallyNoetherian Zo.left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ Zo.hom ‹_›
      (inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K))))
  haveI : GeometricallyReduced Zo.hom := hGR Zo.hom
  haveI : IsReduced (Zo ⊗ Zo).left :=
    (inferInstance : IsReduced (Limits.pullback Zo.hom Zo.hom))
  have hm1 : Set.range ((jo ⊗ₘ jo) ≫ μ[A.X]).left.base ⊆ (Zc : Set A.X.left) := by
    rintro _ ⟨p, rfl⟩
    have hf : (fst A.X A.X).left.base ((jo ⊗ₘ jo).left.base p) =
        ιZ.base ((fst Zo Zo).left.base p) :=
      congrArg (fun φ : Zo ⊗ Zo ⟶ A.X => φ.left.base p) (tensorHom_fst jo jo)
    have hs : (snd A.X A.X).left.base ((jo ⊗ₘ jo).left.base p) =
        ιZ.base ((snd Zo Zo).left.base p) :=
      congrArg (fun φ : Zo ⊗ Zo ⟶ A.X => φ.left.base p) (tensorHom_snd jo jo)
    exact hmul _ (hf ▸ hmem _) (hs ▸ hmem _)
  let m : Zo ⊗ Zo ⟶ Zo := Over.homMk (liftToReduced Zc _ hm1) (by
    change liftToReduced Zc _ hm1 ≫ ιZ ≫ A.X.hom = _
    rw [← Category.assoc, liftToReduced_fac]
    exact Over.w ((jo ⊗ₘ jo) ≫ μ[A.X]))
  have hm' : m ≫ jo = (jo ⊗ₘ jo) ≫ μ[A.X] := Over.OverMorphism.ext (liftToReduced_fac Zc _ hm1)
  -- the inverse
  have hi1 : Set.range (jo ≫ ι[A.X]).left.base ⊆ (Zc : Set A.X.left) := by
    rintro _ ⟨q, rfl⟩
    exact hinv _ (hmem q)
  let i : Zo ⟶ Zo := Over.homMk (liftToReduced Zc _ hi1) (by
    change liftToReduced Zc _ hi1 ≫ ιZ ≫ A.X.hom = _
    rw [← Category.assoc, liftToReduced_fac]
    exact Over.w (jo ≫ ι[A.X]))
  have hi' : i ≫ jo = jo ≫ ι[A.X] := Over.OverMorphism.ext (liftToReduced_fac Zc _ hi1)
  -- the group object
  obtain ⟨inst, hmon⟩ := hGrp A Zo jo e m i he' hm' hi'
  letI := inst
  refine ⟨Grp.mk Zo, jo, hmon, ?_, hRed Zc, hrange, fun x hx => ?_⟩
  · change IsClosedImmersion ιZ
    infer_instance
  · have hx' : Set.range x.left.base ⊆ (Zc : Set A.X.left) := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p (IsLocalRing.closedPoint K)]
      exact hx
    refine ⟨Over.homMk (liftToReduced Zc _ hx') (by
      change liftToReduced Zc _ hx' ≫ ιZ ≫ A.X.hom = _
      rw [← Category.assoc, liftToReduced_fac]
      exact Over.w x), Over.OverMorphism.ext (liftToReduced_fac Zc _ hx')⟩

/-- E3a from its obligations, with the constructor discharged. -/
theorem reducedClosedSubgroup_of (hCO : ClosedUnderOpsOfPoints.{u})
    (hRed : IsReducedSubschemeVanishingIdeal.{u}) (hGrp : GrpObjOfCompatibleMono.{u})
    (hGR : GeomReducedOverAlgClosed.{u}) : ReducedClosedSubgroup.{u} :=
  reducedClosedSubgroup hCO (reducedSubgroupOfClosedSubset hRed hGrp hGR)

end ZInQ.Contrib.CloudR2NOS.Step1
