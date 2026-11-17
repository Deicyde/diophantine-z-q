/-
H5 lane3 Step 2, B1 KEY (K-b.2+3) `LocalizedComapAtHeightOne` (KbPlan.lean fd92404a):
DECOMPOSITION, with the pure-algebra piece (L2) PROVED. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED. Universe u.

Route:
* (L0) Mathlib `IdealSheafData.ideal_comap_of_isOpenImmersion` (an isomorphism is an open
  immersion) gives `(D.comap φ).ideal U = (D.ideal (φ ''ᵁ U)).comap (φ.appIso U).inv`.
* (L1) `StalkIdealTransport` (TRUE): localizing at `p` (point `η`), this is the image of `D`'s
  stalk ideal at `φ η` under the stalk map of `φ` at `η`. It uses `IsAffineOpen.isLocalization_stalk`
  and the independence of the stalk ideal from the affine open, via Mathlib `map_ideal_basicOpen`
  compatibility.
* (L3) `HeightOneLocalizationDVR` (TRUE): `O_{A,η}` is a DVR at height-one `η`, since `A` is
  regular (C5's A2).
* (L2) PROVED below: in a DVR every ideal is fixed by every ring automorphism. Ideals are `⊥` or
  `m^n`, and an automorphism of a local ring maps `m` to `m`.
* (L4) (TRUE): off `supp D`, the stalk ideal is the unit ideal (`support_comap`, and the stalk of
  an ideal sheaf at a point outside its support).
Assembly. If `φ η = η`, the transported stalk ideal is `φ^♯(D_η)`, which equals `D_η` by (L2) and
(L3). If `η, φ η ∉ supp D`, both sides are `⊤` by (L4).
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- (L2), PROVED: ring automorphisms of a DVR fix every ideal. -/
theorem dvr_ideal_map_ringEquiv (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (σ : R ≃+* R) (I : Ideal R) : I.map σ = I := by
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hm : (IsLocalRing.maximalIdeal R).map σ = IsLocalRing.maximalIdeal R := by
    haveI : ((IsLocalRing.maximalIdeal R).map σ).IsMaximal :=
      Ideal.map_isMaximal_of_equiv σ
    exact IsLocalRing.eq_maximalIdeal this
  have hIm : I = (IsLocalRing.maximalIdeal R) ^ n := by
    rw [hn, ← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]
  rw [hIm, Ideal.map_pow, hm]

end ZInQ.Contrib.CloudR2NOS.Step2B1
