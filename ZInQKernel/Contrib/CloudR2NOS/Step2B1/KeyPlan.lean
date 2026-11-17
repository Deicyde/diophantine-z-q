/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B1/KeyPlan.lean (sha256 0b7d2191b67115cbb94ad7d446a506b9df8c09bcd03f31ee974f6f08a564da71).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B1 KEY `ComponentFixingPreservesDivisor` (Plan.lean 205980f8): DECOMPOSITION
into exact native sub-obligations, with truth sketches, plus the assembly PROVED. 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED. Universe u.

(K-a) `CodimOneLocalizationsDetermine` (TRUE): on an abelian variety (regular, hence normal
Noetherian integral, with UFD stalks by C5's A1/A2), two invertible ideal sheaves agree once their
localizations agree at every height-one prime of every affine open.
* A locally principal ideal `(f)` in a Noetherian normal domain is the intersection of its
  localizations at height-one primes (Krull property).
* Equivalently, in a UFD, `(f) = (g)` iff `v_p(f) = v_p(g)` for every prime element `p`.
(K-b) `FixedComponentLocalizations` (TRUE): let `φ` be an automorphism with `φ⁻¹ C = C` for every
component `C` of `supp D`. Then at every height-one prime `p` of every affine `U`, the localizations
of `D.comap φ` and `D` agree.
* If `p ∉ supp D`: both are the unit ideal, since `φ⁻¹(supp D) = supp D`.
* If `p ∈ supp D`: the codimension-1 point `η_p` is the generic point of a component `C` (purity:
  `supp D` has pure codimension 1). `φ` fixes `C` setwise, hence fixes `η_p`, and induces an
  automorphism of the DVR `O_{η_p}`. The localized ideal is `m^n`, and an automorphism preserves
  `m^n`. Hence the localizations agree.
(K-c) `ComapInvertible` (TRUE): `D.comap φ` is invertible for an isomorphism `φ` (flat pullback
of an invertible ideal; W07/Mathlib).
KEY follows from (K-a) applied to `D.comap φ` and `D`, with (K-b) and (K-c).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.Plan

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- (K-a), TRUE (Krull property via UFD stalks, C5's A1/A2). -/
def CodimOneLocalizationsDetermine : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (I J : A.X.left.IdealSheafData), I.IsInvertible → J.IsInvertible →
    (∀ (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
      Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U) =
        Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal)) (J.ideal U)) →
    I = J

/-- (K-b), TRUE (purity plus DVR automorphisms). -/
def FixedComponentLocalizations : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
      (∀ C : Set A.X.left, C ⊆ (D.support : Set A.X.left) →
        Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C →
        (tr A x) ⁻¹' C = C) →
      ∀ (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
        Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal))
            ((D.comap (tr A x)).ideal U) =
          Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal)) (D.ideal U)

/-- (K-c), TRUE: comap of an invertible ideal along a translation is invertible. -/
def ComapInvertible : Prop :=
  ∀ {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, (D.comap (tr A x)).IsInvertible

/-- KEY, PROVED from (K-a), (K-b), (K-c). -/
theorem componentFixingPreservesDivisor (hKa : CodimOneLocalizationsDetermine.{u})
    (hKb : FixedComponentLocalizations.{u}) (hKc : ComapInvertible.{u}) :
    ComponentFixingPreservesDivisor.{u} := by
  intro K _ _ A _ D hD x hfix
  exact hKa A (D.comap (tr A x)) D (hKc A D hD x) hD (hKb A D hD x hfix)

end ZInQ.Contrib.CloudR2NOS.Step2B1
