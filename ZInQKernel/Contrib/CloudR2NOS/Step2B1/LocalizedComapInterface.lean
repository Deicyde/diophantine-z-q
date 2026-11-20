/-
H5 lane3 Step 2, B1 KEY (K-b.2+3): EXACT Props for (L1), (L3) and (L4), frozen for their producers
(lead 05:01Z: (L3) and (L4) go to C2; (L1) stays with lane3). The assembly
`LocalizedComapAtHeightOne` is PROVED from them and (L2) (LocalizedComapPlan.lean 3d7616dc).
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Write `loc_p := algebraMap Γ(U) (Localization.AtPrime p)` and `η := U.2.fromSpec p`.
* (L1) `StalkIdealTransport` (TRUE; lane3): if the isomorphism `φ` fixes `η`, then there is a ring
  automorphism `σ` of `Γ(U)_p` with `loc_p ((D.comap φ).ideal U) = σ (loc_p (D.ideal U))`.
  - `σ` is the automorphism of `O_{A,η} ≅ Γ(U)_p` induced by `φ` (`IsAffineOpen.isLocalization_stalk`).
  - Mathlib `ideal_comap_of_isOpenImmersion` (L0) and the germ/`appIso` compatibility identify
    the two sides.
* (L3) `HeightOneLocalizationDVR` (TRUE; C2): `Γ(U)_p` is a DVR at height-one `p` on an abelian
  variety. It is regular of dimension 1 (C5's A2).
* (L4) `OffSupportLocalizationTop` (TRUE; C2): if `η ∉ supp I`, then `loc_p (I.ideal U) = ⊤`.
  `η ∉ supp I` iff `I.ideal U ⊄ p`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.KbPlan
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.LocalizedComapPlan

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- (L1), TRUE (lane3). -/
def StalkIdealTransport : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (φ : A.X.left ⟶ A.X.left) [IsIso φ]
    (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)),
    φ (U.2.fromSpec p) = U.2.fromSpec p →
      ∃ σ : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime p.asIdeal,
        Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal))
            ((D.comap φ).ideal U) =
          Ideal.map σ (Ideal.map (algebraMap Γ(A.X.left, U.1) (Localization.AtPrime p.asIdeal))
            (D.ideal U))

/-- (L3), TRUE (C2). -/
def HeightOneLocalizationDVR : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
      ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)

/-- (L4), TRUE (C2). -/
def OffSupportLocalizationTop : Prop :=
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)),
    U.2.fromSpec p ∉ (I.support : Set X) →
      Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U) = ⊤

/-- (K-b.2+3) `LocalizedComapAtHeightOne`, PROVED from (L1), (L2), (L3), (L4). -/
theorem localizedComapAtHeightOne (hL1 : StalkIdealTransport.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u}) :
    LocalizedComapAtHeightOne.{u} := by
  intro K _ _ A _ D hD φ _ U p hp hcase
  rcases hcase with ⟨_, hfix⟩ | ⟨hηout, hφηout⟩
  · obtain ⟨σ, hσ⟩ := hL1 A D φ U p hfix
    obtain ⟨hdom, hdvr⟩ := hL3 A U p hp
    rw [hσ]
    exact dvr_ideal_map_ringEquiv (Localization.AtPrime p.asIdeal) σ _
  · have hcomap : U.2.fromSpec p ∉ ((D.comap φ).support : Set A.X.left) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hφηout
    rw [hL4 (D.comap φ) U p hcomap, hL4 D U p hηout]

end ZInQ.Contrib.CloudR2NOS.Step2B1
