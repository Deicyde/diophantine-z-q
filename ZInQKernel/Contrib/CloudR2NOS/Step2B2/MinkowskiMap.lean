/-
H5 lane C3 STEP-F16 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane C3 STEP-F15 fix edition (2026-11-17), superseded by STEP-F16.
-/
/-
H5 lane C3 STEP-F12 fix edition (2026-11-17), superseded by STEP-F15.
-/
/-
H5 lane C3 STEP-H1 public-hygiene edition (2026-11-17): comments only. The code is byte-identical to its base edition; only header and comment text changed.
-/
/-
H5 lane C3 STEP-F2 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane C3 STEP-F1 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane3 Step 2, B2.d (d.1): `MinkowskiMap` (Minkowski.lean (hash in ledger)) PROVED, from C5's
geometric-irreducibility producers, the integral reduced subscheme obligation (C4), and Step 1/2
reduced-lifting lemmas. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.
The construction is in the header of Minkowski.lean.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Minkowski
import ZInQKernel.Contrib.CloudR2NOS.Step1.ConstructorParts
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

open ZInQ.Contrib.CloudR2NOS.Step1 in
theorem minkowskiMap (hInt : IntegralOnIrreducible.{u}) (hGI : GeomIrreducibleOverAlgClosed.{u})
    (hUO : UniversallyOpenOverField.{u}) : MinkowskiMap.{u} := by
  intro K _ _ A _ E F hE hEi hF hFi
  classical
  -- STEP-F12 (pre-emptive): instances at the `Over` forms, each from its concrete form.
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  haveI : Subsingleton (Pt K).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  haveI : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  haveI : IsReduced (Pt K).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  let pt : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) → A.X.left :=
    fun x => x.left (IsLocalRing.closedPoint K)
  let Ec : Closeds A.X.left := ⟨E, hE⟩
  let Fc : Closeds A.X.left := ⟨F, hF⟩
  let ιE := (Scheme.IdealSheafData.vanishingIdeal Ec).subschemeι
  let ιF := (Scheme.IdealSheafData.vanishingIdeal Fc).subschemeι
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Ec).subscheme := hInt Ec hEi
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Fc).subscheme := hInt Fc hFi
  have hrE : Set.range ιE.base = E := range_subschemeι_vanishingIdeal Ec
  have hrF : Set.range ιF.base = F := range_subschemeι_vanishingIdeal Fc
  let Eo : Over (Spec (CommRingCat.of K)) := Over.mk (ιE ≫ A.X.hom)
  let Fo : Over (Spec (CommRingCat.of K)) := Over.mk (ιF ≫ A.X.hom)
  let jE : Eo ⟶ A.X := Over.homMk ιE rfl
  let jF : Fo ⟶ A.X := Over.homMk ιF rfl
  haveI : IrreducibleSpace Eo.left :=
    inferInstanceAs (IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Ec).subscheme)
  haveI : IrreducibleSpace Fo.left :=
    inferInstanceAs (IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Fc).subscheme)
  haveI : LocallyOfFiniteType Eo.hom :=
    (inferInstance : LocallyOfFiniteType (show _ ⟶ Spec (CommRingCat.of K) from ιE ≫ A.X.hom))
  haveI : LocallyOfFiniteType Fo.hom :=
    (inferInstance : LocallyOfFiniteType (show _ ⟶ Spec (CommRingCat.of K) from ιF ≫ A.X.hom))
  haveI : GeometricallyIrreducible Eo.hom := hGI Eo.hom
  haveI : UniversallyOpen Eo.hom := hUO Eo.hom
  haveI hPirr : IrreducibleSpace (Eo ⊗ Fo).left :=
    (inferInstance : IrreducibleSpace ↥(Limits.pullback Eo.hom Fo.hom))
  let m' : Eo ⊗ Fo ⟶ A.X := (fst Eo Fo ≫ jE) * (snd Eo Fo ≫ jF)⁻¹
  refine ⟨(Eo ⊗ Fo).left, hPirr, m'.left, ?_⟩
  -- the value of `m'` after a point `q`
  have hval : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Eo ⊗ Fo,
      q ≫ m' = (q ≫ fst Eo Fo ≫ jE) * (q ≫ snd Eo Fo ≫ jF)⁻¹ := by
    intro q
    rw [MonObj.comp_mul, GrpObj.comp_inv]
  -- lifting rational points of `E` and `F` to the reduced subschemes
  have hlift : ∀ (Zc : Closeds A.X.left) (e : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X),
      pt e ∈ (Zc : Set A.X.left) → Set.range e.left.base ⊆ (Zc : Set A.X.left) := by
    intro Zc e he
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact he
  apply Set.Subset.antisymm
  · -- the Minkowski set lies in the range
    refine closure_mono ?_
    rintro _ ⟨e, f, he, hf, rfl⟩
    let e'' := liftToReduced Ec e.left (hlift Ec e he)
    let f'' := liftToReduced Fc f.left (hlift Fc f hf)
    let eh : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Eo := Over.homMk e'' (by
      change e'' ≫ ιE ≫ A.X.hom = _
      rw [← Category.assoc, liftToReduced_fac]
      exact Over.w e)
    let fh : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Fo := Over.homMk f'' (by
      change f'' ≫ ιF ≫ A.X.hom = _
      rw [← Category.assoc, liftToReduced_fac]
      exact Over.w f)
    have heh : eh ≫ jE = e := Over.OverMorphism.ext (liftToReduced_fac Ec e.left (hlift Ec e he))
    have hfh : fh ≫ jF = f := Over.OverMorphism.ext (liftToReduced_fac Fc f.left (hlift Fc f hf))
    let q := lift eh fh
    have hq : q ≫ m' = e * f⁻¹ := by
      rw [hval, lift_fst_assoc, lift_snd_assoc, heh, hfh]
    refine ⟨q.left (IsLocalRing.closedPoint K), ?_⟩
    change (q.left ≫ m'.left) (IsLocalRing.closedPoint K) = _
    rw [← Over.comp_left, hq]
  · -- the range lies in the closure of the Minkowski set (density of closed points)
    refine closure_minimal ?_ isClosed_closure
    haveI : LocallyOfFiniteType (Eo ⊗ Fo).hom :=
      (inferInstance : LocallyOfFiniteType
        (show _ ⟶ Spec (CommRingCat.of K) from pullback.fst Eo.hom Fo.hom ≫ Eo.hom))
    haveI : JacobsonSpace (Eo ⊗ Fo).left := LocallyOfFiniteType.jacobsonSpace (Eo ⊗ Fo).hom
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ closure (closedPoints (Eo ⊗ Fo).left) := by
      rw [closure_closedPoints]
      trivial
    refine (image_closure_subset_closure_image m'.left.continuous ⟨p, hp, rfl⟩) |>
      fun h => closure_mono ?_ h
    rintro _ ⟨p', hp', rfl⟩
    -- the rational point through `p'`
    let q₀ := pointOfClosedPoint (Eo ⊗ Fo).hom p' hp'
    let q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Eo ⊗ Fo :=
      Over.homMk q₀ (pointOfClosedPoint_comp _ _ _)
    refine ⟨q ≫ fst Eo Fo ≫ jE, q ≫ snd Eo Fo ≫ jF, ?_, ?_, ?_⟩
    · rw [← hrE]
      exact ⟨_, rfl⟩
    · rw [← hrF]
      exact ⟨_, rfl⟩
    · rw [← hval]
      change m'.left p' = (q.left ≫ m'.left) (IsLocalRing.closedPoint K)
      change m'.left p' = m'.left (q₀ (IsLocalRing.closedPoint K))
      -- STEP-F16: the evaluation lemma as a term at the spelled-out point (`q₀` is let-bound).
      exact congrArg (fun z => m'.left z)
        (pointOfClosedPoint_apply (Eo ⊗ Fo).hom p' hp' (IsLocalRing.closedPoint K)).symm

end ZInQ.Contrib.CloudR2NOS.Step2B2
