/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/SeesawBridge.lean (sha256 87559420572fa156a471d0b55304c433f86f72d9b1a6676d9653f9bfde2e02d7).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: the GM1 v3 bridge `AllResidueFibresOfRationalSlices` (SeesawNative.lean).
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

PROVED here, modulo compile:
* `residueFibre_trivial_of_slice`, the closed points.
  - The rational point is `t = pointOfClosedPoint τ = Spec(e) ≫ (Spec κ(τ) → T)`, with
    `e : κ(τ) ≅ K` (Mathlib `residueFieldIsoBase`).
  - The comparison `φ := lift (slice_t) (fX ≫ Spec e) : X ⟶ X_τ` into the residue fibre is an
    ISOMORPHISM. Its inverse is `X_τ → X ×_K T → X`; pullback extensionality uses Mathlib
    `SpecMap_residueFieldIsoBase_inv`.
  - `φ ≫ fibre = slice_t`, so the triviality of the slice transfers by the injectivity of
    `Pic.map φ` (H72 `pic_map_injective_of_isIso`, L1/PicardKernel.lean).
* `allResidueFibresOfRationalSlices (hC)`, the bridge from `TrivialFibreLocusClosed`. The
  trivial-fibre locus is closed and contains every closed point (the part above, Mathlib
  `pointOfClosedPoint_apply`), so it is everything (Jacobson, Mathlib `closure_closedPoints`).

ONE remaining obligation (TRUE), `TrivialFibreLocusClosed`: for the family `X ×_K T → T` with `X`
proper and geometrically integral and `T` locally of finite type, the set of points with trivial
residue fibre is closed.
* Producer of the affine case: H72 `isClosed_fibrePicardClass_trivial`
  (L1/NativeTrivialityLocus.lean fd0f9728…; Noetherian `R`, flat proper geometrically integral).
* Globalization: closedness is local on an affine open cover. Fibres along an open immersion
  agree (H72 L2/RelativeFibreTriviality `fibrePicardClass_baseChange_of_eq_one` and its converse
  via the residue-field isomorphism).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SeesawNative
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The remaining obligation (TRUE; see header). -/
def TrivialFibreLocusClosed : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) [IsProper fX] [GeometricallyIntegral fX]
    [LocallyOfFiniteType fT] (L : (Limits.pullback fX fT).Modules) [L.IsInvertible],
    IsClosed {τ : T | Scheme.Pic.map (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ))
      (Scheme.Pic.mk L) = 1}

/-- PROVED: at a closed point, the residue fibre is trivial if the rational slice is. -/
theorem residueFibre_trivial_of_slice {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fT : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType fT]
    (L : (Limits.pullback fX fT).Modules) [L.IsInvertible] (τ : T) (hτ : IsClosed {τ})
    (hs : Nonempty ((Scheme.Modules.pullback (sliceAt fX fT (pointOfClosedPoint fT τ hτ)
      (pointOfClosedPoint_comp fT τ hτ))).obj L ≅ 𝟙_ X.Modules)) :
    Scheme.Pic.map (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ))
      (Scheme.Pic.mk L) = 1 := by
  let e := residueFieldIsoBase fT τ hτ
  let t := pointOfClosedPoint fT τ hτ
  have ht : t ≫ fT = 𝟙 _ := pointOfClosedPoint_comp fT τ hτ
  have htdef : t = Spec.map e.hom ≫ T.fromSpecResidueField τ := rfl
  let p := pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ)
  let q := pullback.snd (pullback.snd fX fT) (T.fromSpecResidueField τ)
  have hcond : sliceAt fX fT t ht ≫ pullback.snd fX fT =
      (fX ≫ Spec.map e.hom) ≫ T.fromSpecResidueField τ := by
    rw [pullback.lift_snd, Category.assoc, ← htdef]
  let φ : X ⟶ Limits.pullback (pullback.snd fX fT) (T.fromSpecResidueField τ) :=
    pullback.lift (sliceAt fX fT t ht) (fX ≫ Spec.map e.hom) hcond
  have hφp : φ ≫ p = sliceAt fX fT t ht := pullback.lift_fst _ _ _
  have hφq : φ ≫ q = fX ≫ Spec.map e.hom := pullback.lift_snd _ _ _
  -- `q` factors through the structure map, via the residue-field isomorphism
  have hq : (p ≫ pullback.fst fX fT ≫ fX) ≫ Spec.map e.hom = q := by
    have h1 : q ≫ Spec.map e.inv = p ≫ pullback.fst fX fT ≫ fX := by
      rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc, ← pullback.condition,
        Category.assoc, ← pullback.condition]
    rw [← h1, Category.assoc, ← Spec.map_comp, e.hom_inv_id, Spec.map_id, Category.comp_id]
  have hinv₁ : φ ≫ (p ≫ pullback.fst fX fT) = 𝟙 X := by
    rw [← Category.assoc, hφp, pullback.lift_fst]
  have hinv₂ : (p ≫ pullback.fst fX fT) ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφp, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, htdef, pullback.condition, ← hq]
        simp only [Category.assoc]
    · rw [Category.assoc, hφq, Category.id_comp, ← hq]
      simp only [Category.assoc]
  haveI : IsIso φ := ⟨⟨p ≫ pullback.fst fX fT, hinv₁, hinv₂⟩⟩
  apply ZInQ.Contrib.CloudR2Poincare.L1.pic_map_injective_of_isIso φ
  rw [← Scheme.Pic.map_comp, hφp, Scheme.Pic.map_one, Scheme.Pic.map_mk, Scheme.Pic.one_eq_mk_unit]
  exact (Scheme.Pic.mk_eq_mk_iff _ _).mpr hs

/-- The bridge, PROVED from `TrivialFibreLocusClosed`. -/
theorem allResidueFibresOfRationalSlices (hC : TrivialFibreLocusClosed.{u}) :
    AllResidueFibresOfRationalSlices.{u} := by
  intro K _ _ X T fX fT _ _ _ L _ hslice τ
  haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace fT
  let S : Set T := {τ : T | Scheme.Pic.map
    (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ)) (Scheme.Pic.mk L) = 1}
  have hS : IsClosed S := hC fX fT L
  have hclosed : closedPoints T ⊆ S := fun x hx =>
    residueFibre_trivial_of_slice fX fT L x hx (hslice _ _)
  have huniv : S = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints]
    exact hS.closure_subset_iff.mpr hclosed
  have hτ : τ ∈ S := by rw [huniv]; exact Set.mem_univ τ
  exact hτ

/-- GM1 v3 with the bridge reduced: from `TrivialFibreLocusClosed`. -/
theorem seesawPulledBack_v3' (hC : TrivialFibreLocusClosed.{u}) : SeesawPulledBack.{u} :=
  seesawPulledBack_v3 (allResidueFibresOfRationalSlices hC)

end ZInQ.Contrib.CloudR2NOS.Step1
