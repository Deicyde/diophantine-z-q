/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

The generic open is ACTUALLY Spec of the original fraction field K of the
original DVR R, with the original algebraMap retained. This supplies the
V ≅ Spec K input to GenericBaseChange instead of assuming an unrelated
field/open iso, a Type-0 DVR, or any perfectness/characteristic hypothesis.
No henselization/closure is reconstructed here (that remains H4's supplier).
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The ORIGINAL fraction field of a DVR is localization at ANY actual
    uniformizer. Surjectivity is proved from the native unit×power form. -/
theorem dvr_fractionField_isLocalizationAway
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (π : R) (hπ : Irreducible π) :
    IsLocalization.Away π K := by
  have hp : algebraMap R K π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, n, rfl⟩
    simpa only [map_pow] using (IsUnit.mk0 (algebraMap R K π) hp).pow n
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0 : b ≠ 0 := by simpa using hb
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := b) hb0 hπ
    refine ⟨⟨(↑w⁻¹ : R) * a, ⟨π ^ n, n, rfl⟩⟩, ?_⟩
    change (algebraMap R K a / algebraMap R K b) * algebraMap R K (π ^ n) =
      algebraMap R K ((↑w⁻¹ : R) * a)
    have hu : algebraMap R K (w : R) ≠ 0 := (w.isUnit.map (algebraMap R K)).ne_zero
    have hn : algebraMap R K (π ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero n hp
    apply mul_left_cancel₀ hu
    calc
      algebraMap R K (w : R) * ((algebraMap R K a / algebraMap R K b) * algebraMap R K (π ^ n)) =
          (algebraMap R K a / (algebraMap R K (w : R) * algebraMap R K (π ^ n))) *
            (algebraMap R K (w : R) * algebraMap R K (π ^ n)) := by rw [hw, map_mul]; ring
      _ = algebraMap R K a := div_mul_cancel₀ _ (mul_ne_zero hu hn)
      _ = algebraMap R K (w : R) * algebraMap R K ((↑w⁻¹ : R) * a) := by
        simp only [map_mul, ← mul_assoc, ← map_mul]
        simp
  · intro x y hxy
    have h : x = y := (IsFractionRing.injective R K) hxy
    exact ⟨1, by rw [h]⟩

/-- Canonical generic open of the ORIGINAL DVR and its ORIGINAL fraction
    field: the actual Spec(algebraMap) triangle and one closed complement. -/
theorem exists_dvr_genericOpen_originalField
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ (V : (Spec (CommRingCat.of R)).Opens) (i : V.toScheme ≅ Spec (CommRingCat.of K)),
      i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = V.ι ∧
      ∀ z : Spec (CommRingCat.of R), z ∉ V → z = IsLocalRing.closedPoint R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away π K := dvr_fractionField_isLocalizationAway R K π hπ
  let j : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization π
  let V := j.opensRange
  let i : V.toScheme ≅ Spec (CommRingCat.of K) := j.isoOpensRange.symm
  refine ⟨V, i, ?_, ?_⟩
  · change j.isoOpensRange.inv ≫ j = j.opensRange.ι
    calc
      j.isoOpensRange.inv ≫ j =
          j.isoOpensRange.inv ≫ (j.isoOpensRange.hom ≫ j.opensRange.ι) :=
        congrArg (j.isoOpensRange.inv ≫ ·) (Scheme.Hom.isoOpensRange_hom_ι j).symm
      _ = j.opensRange.ι := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · intro s hs
    let z : Spec (CommRingCat.of K) := default
    have hz0 : z.asIdeal = (⊥ : Ideal K) :=
      (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
    have hjz : (j z).asIdeal = (⊥ : Ideal R) := by
      change Ideal.comap (algebraMap R K) z.asIdeal = ⊥
      rw [hz0]
      change RingHom.ker (algebraMap R K) = ⊥
      ext x
      change algebraMap R K x = 0 ↔ x = 0
      constructor
      · intro h
        exact (IsFractionRing.injective R K) (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hsid : s.asIdeal ≠ (⊥ : Ideal R) := by
      intro h
      apply hs
      change s ∈ Set.range j
      refine ⟨z, ?_⟩
      apply PrimeSpectrum.ext
      exact hjz.trans h.symm
    obtain ⟨P, hP, hUnique⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance |>.2
    have hsP : s.asIdeal = P := hUnique _ ⟨hsid, s.isPrime⟩
    have hcP : IsLocalRing.maximalIdeal R = P :=
      hUnique _ ⟨IsDiscreteValuationRing.not_a_field R, inferInstance⟩
    apply PrimeSpectrum.ext
    exact hsP.trans hcP.symm

#print axioms dvr_fractionField_isLocalizationAway
#print axioms exists_dvr_genericOpen_originalField

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
