/-
H5 lane3 Step 1: R1 v2 (`RelativeVanishingSectionsCore`, `RelativeDetectionSections`) PROVED
from ONE heavy obligation and two small biproduct facts. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED. Universe u.

Heavy obligation (TRUE), `FieldBaseChangeFreeDirectImage`: for `fX` proper over a field `K`
(separated, locally of finite presentation over `K`) and `F` finitely presented, every
`fY : Y ⟶ Spec K` has `R^q pr₂_*(pr₁^*F) ≅ ⨁_{Fin h} O_Y` GLOBALLY, where `h = h^q(X, F)`.
Route (W07 only; lead preference 04:09Z):
1. W07 `exists_isFiniteFreeComplex_higherDirectImage` (FiniteFreeModelBaseChange). Over `Spec K`
   its open contains the only point, so it is `⊤`. It gives a global iso with `H^q(fY^*K•)`,
   `K•` a finite free complex (`IsFiniteFreeComplex`). Every module is flat over a field.
2. `fY` is flat, so `pullback fY` is exact (W07 Modules/FlatPullback:79), and
   `H^q(fY^*K•) ≅ fY^*H^q(K•)` (`ShortComplex.mapHomologyIso`).
3. `H^q(K•)` is a finite module on `Spec K`, hence `≅ O^h`. Comparing with the identity base
   change and W07 `exists_bijective_semilinearMap_sections_higherDirectImage_H` (affine base,
   separated `fX`) gives `h = finrank H^q(X, F)`. Pullback preserves finite biproducts and `O`.
Small obligations (TRUE; additive-functor facts):
* `BiproductUnitTensorSections`: `Γ((⨁ O) ⊗ G) = 0` when `Γ(G) = 0`. Tensoring preserves
  biproducts, `O ⊗ G ≅ G`, and `H⁰` is additive.
* `BiproductUnitSectionsNontrivial`: `Γ(⨁_{Fin h} O_Y) ≠ 0` for `h > 0` and `Y ≠ ∅`, since it
  contains `Γ(O_Y) ∋ 1 ≠ 0`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.HigherProjectionFormula

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The heavy obligation (TRUE; route in the header). -/
def FieldBaseChangeFreeDirectImage : Prop :=
  ∀ {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [IsSeparated fX] [IsProper fX]
    [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ),
    Nonempty ((higherDirectImage (pullback.snd fX fY) q).obj
        ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F) ≅
      ⨁ (fun _ : Fin (letI : X.Over (Spec (CommRingCat.of K)) := ⟨fX⟩; F.finrankH K q) =>
        𝟙_ Y.Modules))

/-- Small obligation (TRUE). -/
def BiproductUnitTensorSections : Prop :=
  ∀ {Y : Scheme.{u}} (h : ℕ) (G : Y.Modules), Subsingleton (G.H 0) →
    Subsingleton (((⨁ (fun _ : Fin h => 𝟙_ Y.Modules)) ⊗ G).H 0)

/-- Small obligation (TRUE). -/
def BiproductUnitSectionsNontrivial : Prop :=
  ∀ {Y : Scheme.{u}} [Nonempty Y] (h : ℕ), 0 < h →
    ¬ Subsingleton ((⨁ (fun _ : Fin h => 𝟙_ Y.Modules)).H 0)

theorem Subsingleton_H_zero_of_iso {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (h : Subsingleton (B.H 0)) : Subsingleton (A.H 0) :=
  (Scheme.Modules.H.mapLinearEquiv e 0).toEquiv.subsingleton

/-- R1a core, PROVED from the obligations. -/
theorem relativeVanishingSectionsCore (hFB : FieldBaseChangeFreeDirectImage.{u})
    (hT : BiproductUnitTensorSections.{u}) : RelativeVanishingSectionsCore.{u} := by
  intro K _ X Y fX fY _ _ _ _ _ _ F _ _ G _ q hG
  obtain ⟨e⟩ := hFB fX fY F q
  exact Subsingleton_H_zero_of_iso (tensorIso e (Iso.refl G)) (hT _ G hG)

/-- R1b, PROVED from the obligations. -/
theorem relativeDetectionSections (hFB : FieldBaseChangeFreeDirectImage.{u})
    (hN : BiproductUnitSectionsNontrivial.{u}) : RelativeDetectionSections.{u} := by
  intro K _ X Y fX fY _ _ _ _ _ _ _ F _ _ q hsub
  obtain ⟨e⟩ := hFB fX fY F q
  by_contra hne
  exact hN _ (Nat.pos_of_ne_zero hne) (Subsingleton_H_zero_of_iso e.symm hsub)

end ZInQ.Contrib.CloudR2NOS.Step1
