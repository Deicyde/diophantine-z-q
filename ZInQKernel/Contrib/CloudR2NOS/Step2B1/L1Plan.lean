/-
H5 lane3 Step 2, B1 KEY (L1) `StalkIdealTransport` (LocalizedComapInterface.lean f74bd528):
DECOMPOSITION into two bookkeeping sub-obligations, with the assembly PROVED. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

* (L1.a) `StalkIdealIndependent` (TRUE): two affine charts `(U, p)` and `(V, q)` of the same point
  `x` have isomorphic localizations, by a ring isomorphism matching the localized ideals of any
  ideal sheaf. Both are the stalk `O_x` (`IsAffineOpen.isLocalization_stalk`). The localized
  ideals are both the stalk ideal: compare on a common basic open via Mathlib
  `IdealSheafData.map_ideal_basicOpen`.
* (L1.b) `ComapLocalizationIso` (TRUE): for an isomorphism `φ` and a chart `(U, p)` of `η`, there is
  a chart `(V, q)` of `φ η` and a ring isomorphism `ρ : Γ(U)_p ≃ Γ(V)_q` that sends the localized
  comap ideal to the localized ideal. Here `V = φ ''ᵁ U`, `ρ` is the localization of
  `(φ.appIso U).inv`, and Mathlib `ideal_comap_of_isOpenImmersion` is used.
* (L1) from these, when `φ η = η`: `σ := ρ.symm ∘ τ`, with `τ` from (L1.a) for the charts `(U, p)`
  and `(V, q)` of `η = φ η`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.LocalizedComapInterface

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- (L1.a), TRUE. -/
def StalkIdealIndependent : Prop :=
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (U V : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1))
    (q : PrimeSpectrum Γ(X, V.1)), U.2.fromSpec p = V.2.fromSpec q →
      ∃ τ : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal,
        Ideal.map τ (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U)) =
          Ideal.map (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)) (I.ideal V)

/-- (L1.b), TRUE. -/
def ComapLocalizationIso : Prop :=
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (φ : X ⟶ X) [IsIso φ] (U : X.affineOpens)
    (p : PrimeSpectrum Γ(X, U.1)),
    ∃ (V : X.affineOpens) (q : PrimeSpectrum Γ(X, V.1)),
      V.2.fromSpec q = φ (U.2.fromSpec p) ∧
      ∃ ρ : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal,
        Ideal.map ρ (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal))
            ((I.comap φ).ideal U)) =
          Ideal.map (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)) (I.ideal V)

/-- (L1), PROVED from (L1.a) and (L1.b). -/
theorem stalkIdealTransport (ha : StalkIdealIndependent.{u}) (hb : ComapLocalizationIso.{u}) :
    StalkIdealTransport.{u} := by
  intro K _ _ A _ D φ _ U p hfix
  obtain ⟨V, q, hVq, ρ, hρ⟩ := hb D φ U p
  obtain ⟨τ, hτ⟩ := ha D U V p q (hVq.trans hfix).symm
  refine ⟨τ.trans ρ.symm, ?_⟩
  have h1 : Ideal.map ρ.symm (Ideal.map ρ (Ideal.map (algebraMap Γ(A.X.left, U.1)
      (Localization.AtPrime p.asIdeal)) ((D.comap φ).ideal U))) =
        Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal))
          ((D.comap φ).ideal U) := by
    rw [Ideal.map_map]
    simp
  rw [← h1, hρ, ← hτ, Ideal.map_map]
  rfl

end ZInQ.Contrib.CloudR2NOS.Step2B1
