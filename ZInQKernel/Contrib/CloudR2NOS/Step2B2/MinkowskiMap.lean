/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step-fix1/ZInQKernel/Contrib/CloudR2NOS/Step2B2/MinkowskiMap.lean (sha256 ec135fdf148fb6a5c53469b3a7927cda135eb42a7bcc41ce2334e1ff02d25706).
Body change relative to the base: ONLY P5, the line `open CategoryTheory.CartesianMonoidalCategory` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B2/MinkowskiMap.lean (sha256 d6c7586fa6164934f63be48f58a09ca81e9c547008d3f190b903ac56be8a24d2).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B2.d (d.1): `MinkowskiMap` (Minkowski.lean d42be255) PROVED, from C5's
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
  haveI : LocallyOfFiniteType Eo.hom := inferInstance
  haveI : LocallyOfFiniteType Fo.hom := inferInstance
  haveI : GeometricallyIrreducible Eo.hom := hGI Eo.hom
  haveI : UniversallyOpen Eo.hom := hUO Eo.hom
  haveI hPirr : IrreducibleSpace (Eo ⊗ Fo).left :=
    (inferInstance : IrreducibleSpace (Limits.pullback Eo.hom Fo.hom))
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
    let ê : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Eo := Over.homMk e'' (by
      change e'' ≫ ιE ≫ A.X.hom = _
      rw [← Category.assoc, liftToReduced_fac]
      exact Over.w e)
    let f̂ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Fo := Over.homMk f'' (by
      change f'' ≫ ιF ≫ A.X.hom = _
      rw [← Category.assoc, liftToReduced_fac]
      exact Over.w f)
    have hê : ê ≫ jE = e := Over.OverMorphism.ext (liftToReduced_fac Ec e.left (hlift Ec e he))
    have hf̂ : f̂ ≫ jF = f := Over.OverMorphism.ext (liftToReduced_fac Fc f.left (hlift Fc f hf))
    let q := lift ê f̂
    have hq : q ≫ m' = e * f⁻¹ := by
      rw [hval, lift_fst_assoc, lift_snd_assoc, hê, hf̂]
    refine ⟨q.left (IsLocalRing.closedPoint K), ?_⟩
    change (q.left ≫ m'.left) (IsLocalRing.closedPoint K) = _
    rw [← Over.comp_left, hq]
  · -- the range lies in the closure of the Minkowski set (density of closed points)
    refine closure_minimal ?_ isClosed_closure
    haveI : LocallyOfFiniteType (Eo ⊗ Fo).hom := inferInstance
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
      rw [pointOfClosedPoint_apply]

end ZInQ.Contrib.CloudR2NOS.Step2B2
