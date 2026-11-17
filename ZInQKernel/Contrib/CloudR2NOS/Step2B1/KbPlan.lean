/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B1/KbPlan.lean (sha256 fd92404a77e28eb7f9092b46368a0ddb64317f66d95251d5e180cf67040f2c7c).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B1 KEY (K-b) `FixedComponentLocalizations` (KeyPlan.lean 0b7d2191):
DECOMPOSITION into exact native sub-obligations, with truth sketches, and the assembly PROVED.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

For an affine `U` and a height-one prime `p` of `Γ(U)`, write `η := U.2.fromSpec p` and
`φ := t_x`.
(K-b.1) `HeightOnePointBehaviour` (TRUE):
* If `η ∈ supp D`, then `η` is the generic point of a component `C` of `supp D`. This is purity
  (C5's (d.2) Krull PIT): `supp D` has pure codimension 1, and `η` has codimension 1. `φ⁻¹ C = C`
  forces `φ η = η`.
* If `η ∉ supp D`, then `φ η ∉ supp D`, because `φ⁻¹ supp D = supp D`. That equality follows from
  component-fixing and `PointsOfSupportInComponents`.
(K-b.2) `LocalizedComapAtFixedPoint` (TRUE): if `φ η = η`, the localization of `D.comap φ` at `p`
is the image of the localization of `D` at `p` under the local automorphism induced by `φ` at
`η`. In a DVR (K-b.3) every ideal is `⊥` or `m^n`, and a local automorphism preserves `m^n`, so the
two localizations agree. If `η ∉ supp D` and `φ η ∉ supp D`, both are the unit ideal.
(K-b.3) `HeightOneLocalizationDVR` (TRUE): `Γ(U)_p` is a DVR. `A` is regular, so `O_{A,η}` is
regular local of dimension 1 (Mathlib `IsAffineOpen.isLocalization_stalk`, C5's A2).
Below, (K-b.2) is stated in its combined form (all three facts merged), which is what (K-b) needs.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.KeyPlan
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.Assembly

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- (K-b.1), TRUE: behaviour of a component-fixing translation at height-one points. -/
def HeightOnePointBehaviour : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
      (∀ C : Set A.X.left, C ⊆ (D.support : Set A.X.left) →
        Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C →
        (tr A x) ⁻¹' C = C) →
      ∀ (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
        (U.2.fromSpec p ∈ (D.support : Set A.X.left) → tr A x (U.2.fromSpec p) = U.2.fromSpec p) ∧
        (U.2.fromSpec p ∉ (D.support : Set A.X.left) →
          tr A x (U.2.fromSpec p) ∉ (D.support : Set A.X.left))

/-- (K-b.2 + K-b.3, combined), TRUE: at a height-one point that the automorphism either fixes or
keeps off the support, the localizations of the comap and of `D` agree. -/
def LocalizedComapAtHeightOne : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ (φ : A.X.left ⟶ A.X.left) [IsIso φ] (U : A.X.left.affineOpens)
      (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
      ((U.2.fromSpec p ∈ (D.support : Set A.X.left) ∧ φ (U.2.fromSpec p) = U.2.fromSpec p) ∨
        (U.2.fromSpec p ∉ (D.support : Set A.X.left) ∧
          φ (U.2.fromSpec p) ∉ (D.support : Set A.X.left))) →
      Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal))
          ((D.comap φ).ideal U) =
        Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal)) (D.ideal U)

/-- (K-b), PROVED from (K-b.1) and the combined (K-b.2/3). -/
theorem fixedComponentLocalizations (h1 : HeightOnePointBehaviour.{u})
    (h2 : LocalizedComapAtHeightOne.{u}) : FixedComponentLocalizations.{u} := by
  intro K _ _ A _ D hD x hfix U p hp
  haveI : IsIso (tr A x) := ⟨⟨tr A x⁻¹, by
      rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, mul_inv_cancel,
        ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one], by
      rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, inv_mul_cancel,
        ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one]⟩⟩
  obtain ⟨hin, hout⟩ := h1 A D hD x hfix U p hp
  refine h2 A D hD (tr A x) U p hp ?_
  by_cases hη : U.2.fromSpec p ∈ (D.support : Set A.X.left)
  · exact Or.inl ⟨hη, hin hη⟩
  · exact Or.inr ⟨hη, hout hη⟩

end ZInQ.Contrib.CloudR2NOS.Step2B1
