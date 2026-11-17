/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-1 producer item for C3: `FieldBaseChangeFreeDirectImage` (C3 `Step1/R1Core.lean`
83fae2f4, statement used verbatim through the import), PROVED natively from W07 + Mathlib.
SOURCE ONLY, UNCOMPILED. Native HELD. No kernel/ABI/admission grade.

For `fX : X ⟶ Spec K` separated and proper and `F` finitely presented quasi-coherent, every
`fY : Y ⟶ Spec K` has `R^q pr₂_*(pr₁^* F) ≅ ⨁_{Fin h} 𝒪_Y` GLOBALLY, `h = h^q(X, F)`.

Route (C3/lead plan, W07 only):
1. sub-obligations: every quasi-coherent `F` is relatively flat over a field
   (`isFlatOver_of_field`, via W07 `isFlatOver_of_forall_exists_nhds`: a base affine open meeting
   the image is `⊤`, whose ring is a field by Mathlib `isField_of_isIntegral_of_subsingleton`);
   `LocallyOfFinitePresentation fX` is the Mathlib instance from finite type over a Noetherian
   base; `fY` is flat (Mathlib instance for integral subsingleton targets).
2. W07 `exists_isFiniteFreeComplex_higherDirectImage` at the unique point: the open is `⊤`, so
   one finite free complex `K•` computes all base changes. With `b = (⊤.ι)⁻¹`:
   identity square ⇒ `H^q(b^*K•) ≅ R^q fX_* F`; the `fY`-square ⇒
   `H^q((fY ≫ b)^*K•) ≅ R^q pr₂_*(pr₁^*F)`.
3. `fY^*` preserves homology (W07 FlatPullback) and `(fY ≫ b)^* ≅ b^* ⋙ fY^*`, so
   `R^q pr₂_*(pr₁^*F) ≅ fY^*(R^q fX_* F)`.
4. On `Spec K`, `Γ(R^q fX_* F) ≃ₗ H^q(X, F)` (W07), finite (W07 `hasFiniteH_of_isProper`), so
   `R^q fX_* F ≅ free (Fin h)` by the W07 equivalence `moduleSpecΓFunctor` over a field; free
   pulls back to free (W07 `pullbackFreeIso`), and `free (Fin h) ≅ ⨁_{Fin h} 𝟙`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.R1Core
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModelBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Flat.Local
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FlatPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Field
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeComplex
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Free
import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.FieldBaseChange

variable {K : Type u} [Field K]

/-- **Sub-obligation.** Every quasi-coherent module is relatively flat over a field. -/
theorem isFlatOver_of_field {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (F : X.Modules) [F.IsQuasicoherent] : F.IsFlatOver fX := by
  refine Scheme.Modules.isFlatOver_of_forall_exists_nhds fX F fun V x hx =>
    ⟨⊤, trivial, fun U hU _ => ?_⟩
  have hV : V.1 = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : y = fX.base x := Subsingleton.elim _ _
    rw [hy]
    exact hx
  have hfield : IsField Γ(Spec (CommRingCat.of K), V.1) := by
    rw [hV]
    exact isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))
  dsimp only
  letI := hfield.toField
  infer_instance

/-- `free (ULift (Fin h)) ≅ ⨁_{Fin h} 𝟙` on any scheme. -/
noncomputable def freeIsoBiproduct {Z : Scheme.{u}} (h : ℕ) :
    SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin h)) ≅
      ⨁ (fun _ : Fin h => 𝟙_ Z.Modules) :=
  (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin h) ≃ Fin h).symm
      (fun _ : ULift.{u} (Fin h) => SheafOfModules.unit Z.ringCatSheaf)).symm ≪≫
    (biproduct.isoCoproduct (fun _ : Fin h => 𝟙_ Z.Modules)).symm

/-- **Sub-obligation.** A module on `Spec K` whose global sections are finite of dimension `h`
is free of rank `h` (W07 equivalence `moduleSpecΓFunctor` over a field). -/
theorem nonempty_iso_free_of_finrank (M : (Spec (CommRingCat.of K)).Modules)
    [Module.Finite K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj M)] {h : ℕ}
    (hM : Module.finrank K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj M) = h) :
    Nonempty (M ≅ SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
      (ULift.{u} (Fin h))) := by
  have := isEquivalence_moduleSpecΓFunctor (R := CommRingCat.of K) (Field.toIsField K)
  obtain ⟨hN, hNfin⟩ := Scheme.Modules.finrank_moduleSpecΓFunctor_obj_free (Field.toIsField K)
    (Iso.refl (SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
      (ULift.{u} (Fin h))))
  simp only [Fintype.card_ulift, Fintype.card_fin] at hN
  haveI : Module.Finite K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      (SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
        (ULift.{u} (Fin h)))) := hNfin
  exact ⟨(moduleSpecΓFunctor (R := CommRingCat.of K)).preimageIso
    (LinearEquiv.ofFinrankEq _ _ (hM.trans hN.symm)).toModuleIso⟩

/-- The direct image over `Spec K` is free of rank `h^q(X, F)`. -/
theorem nonempty_higherDirectImage_iso_free {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    [IsSeparated fX] [IsProper fX] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFinitePresentation] (q : ℕ) :
    Nonempty ((higherDirectImage fX q).obj F ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
        (ULift.{u} (Fin (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; F.finrankH K q)))) := by
  letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩
  have := Scheme.Modules.isGrothendieckAbelian X
  haveI : QuasiCompact (X ↘ Spec (CommRingCat.of K)) := inferInstanceAs (QuasiCompact fX)
  haveI : IsSeparated (X ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsSeparated fX)
  obtain ⟨e⟩ := Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H
    F K q
  haveI : Module.Finite K (F.H q) := Scheme.Modules.hasFiniteH_of_isProper fX F q
  haveI : Module.Finite K ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((higherDirectImage fX q).obj F)) := Module.Finite.equiv e.symm
  exact nonempty_iso_free_of_finrank ((higherDirectImage fX q).obj F) e.finrank_eq

/-- **`FieldBaseChangeFreeDirectImage`, in C3's exact form.** -/
theorem fieldBaseChangeFreeDirectImage_core {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K)) [IsSeparated fX]
    [IsProper fX] [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    Nonempty ((higherDirectImage (pullback.snd fX fY) q).obj
        ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F) ≅
      ⨁ (fun _ : Fin (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; F.finrankH K q) =>
        𝟙_ Y.Modules)) := by
  have := Scheme.Modules.isGrothendieckAbelian X
  -- the universal finite free model at the unique point of `Spec K`
  have hflat := isFlatOver_of_field fX F
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨U, Kc, d, hpt, -, hcomp⟩ :=
    Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage fX F hflat pt
  have hU : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    rwa [Subsingleton.elim y pt]
  subst hU
  haveI : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
  let b : Spec (CommRingCat.of K) ⟶ (⊤ : (Spec (CommRingCat.of K)).Opens).toScheme :=
    inv (⊤ : (Spec (CommRingCat.of K)).Opens).ι
  have hb : b ≫ (⊤ : (Spec (CommRingCat.of K)).Opens).ι = 𝟙 _ := IsIso.inv_hom_id _
  -- (i) the identity square: the model computes `R^q fX_* F`
  have sq1 : IsPullback (𝟙 X) fX fX (b ≫ (⊤ : (Spec (CommRingCat.of K)).Opens).ι) := by
    rw [hb]
    exact IsPullback.id_horiz fX
  obtain ⟨c1⟩ := hcomp b (𝟙 X) fX sq1 q
  -- (ii) the `fY` square: the model computes `R^q pr₂_*(pr₁^* F)`
  have sq2 : IsPullback (pullback.fst fX fY) (pullback.snd fX fY) fX
      ((fY ≫ b) ≫ (⊤ : (Spec (CommRingCat.of K)).Opens).ι) := by
    rw [Category.assoc, hb, Category.comp_id]
    exact IsPullback.of_hasPullback fX fY
  obtain ⟨c2⟩ := hcomp (fY ≫ b) (pullback.fst fX fY) (pullback.snd fX fY) sq2 q
  -- (iii) compare the pulled-back complexes and commute homology with the flat `fY^*`
  let Kb := ((Scheme.Modules.pullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj Kc
  let cc : ((Scheme.Modules.pullback fY).mapHomologicalComplex (ComplexShape.up ℤ)).obj Kb ≅
      ((Scheme.Modules.pullback (fY ≫ b)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Kc :=
    (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp fY b)
      (ComplexShape.up ℤ)).app Kc
  let hH : (((Scheme.Modules.pullback fY).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        Kb).homology (q : ℤ) ≅ (Scheme.Modules.pullback fY).obj (Kb.homology (q : ℤ)) :=
    (Kb.sc (q : ℤ)).mapHomologyIso (Scheme.Modules.pullback fY)
  -- (iv) the direct image over `Spec K` is free of rank `h^q`
  obtain ⟨φ⟩ := nonempty_higherDirectImage_iso_free fX F q
  let E1 : Kb.homology (q : ℤ) ≅ (higherDirectImage fX q).obj F :=
    c1 ≪≫ (higherDirectImage fX q).mapIso ((Scheme.Modules.pullbackId X).app F)
  exact ⟨c2.symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (q : ℤ)).mapIso cc.symm ≪≫
    hH ≪≫ (Scheme.Modules.pullback fY).mapIso (E1 ≪≫ φ) ≪≫
    Scheme.Modules.pullbackFreeIso fY _ ≪≫ freeIsoBiproduct _⟩

/-- **C3's `FieldBaseChangeFreeDirectImage` (R1Core 83fae2f4), proved.** -/
theorem fieldBaseChangeFreeDirectImage :
    ZInQ.Contrib.CloudR2NOS.Step1.FieldBaseChangeFreeDirectImage.{u} := by
  intro K _ X Y fX fY _ _ _ F _ _ q
  exact fieldBaseChangeFreeDirectImage_core fX fY F q

end ZInQ.Contrib.CloudR2NOS.ClosedSection.FieldBaseChange
