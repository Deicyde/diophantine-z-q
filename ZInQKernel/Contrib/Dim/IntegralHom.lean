import ZInQKernel.Contrib.Dim.Basic

/-!
# Integral maps and Krull dimension

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting tasks g0-dim and infra-smooth-dim). Mathlib only.

## Main results

* `ZInQ.Contrib.Dim.ringKrullDim_le_of_isIntegral`: an integral ring map `A → B` gives
  `dim B ≤ dim A` (incomparability).
* `ZInQ.Contrib.Dim.ringKrullDim_eq_of_isIntegral_of_injective`: an injective integral ring map
  gives `dim B = dim A` (incomparability and going up).
* `ZInQ.Contrib.Dim.topologicalKrullDim_le_of_isIntegralHom`: an integral morphism of schemes
  `f : X ⟶ Y` gives `dim X ≤ dim Y`.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_isIntegralHom_of_surjective`: a surjective integral
  morphism (for example a finite surjective morphism, such as an isogeny) gives `dim X = dim Y`.
-/

namespace ZInQ.Contrib.Dim

open Order

/-- An integral ring map does not raise the Krull dimension: `dim B ≤ dim A` (incomparability). -/
theorem ringKrullDim_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.IsIntegral) : ringKrullDim B ≤ ringKrullDim A := by
  let _ := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
  intro P Q hPQ
  have h : P.asIdeal < Q.asIdeal := hPQ
  exact Ideal.IsIntegral.under_lt_under (R := A) h

/-- An injective integral ring map preserves the Krull dimension: `dim B = dim A`
(incomparability and going up). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · exact ringKrullDim_le_of_isIntegral (algebraMap A B) (Algebra.IsIntegral.isIntegral (R := A))
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

open AlgebraicGeometry CategoryTheory Limits

/-- An integral morphism of affine schemes does not raise the dimension. -/
theorem topologicalKrullDim_le_of_isIntegralHom_of_isAffine {Z W : Scheme} [IsAffine Z]
    [IsAffine W] (g : Z ⟶ W) [IsIntegralHom g] :
    topologicalKrullDim Z ≤ topologicalKrullDim W := by
  have h : IsIntegralHom (Z.isoSpec.inv ≫ g ≫ W.isoSpec.hom) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Z.isoSpec.inv ≫ g ≫ W.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ, IsIntegralHom.SpecMap_iff] at h
  rw [topologicalKrullDim_eq_of_iso Z.isoSpec, topologicalKrullDim_eq_of_iso W.isoSpec,
    topologicalKrullDim_spec, topologicalKrullDim_spec]
  exact ringKrullDim_le_of_isIntegral _ h

/-- **An integral morphism of schemes does not raise the dimension.** -/
theorem topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_scheme_eq_iSup_cover Y.affineCover,
    topologicalKrullDim_scheme_eq_iSup_cover (Y.affineCover.pullback₁ f)]
  refine iSup_mono fun i => ?_
  show topologicalKrullDim (pullback (C := Scheme) f (Y.affineCover.f i)) ≤ _
  have : IsAffine (Y.affineCover.X i) := Scheme.isAffine_affineCover Y i
  have : IsAffine (pullback (C := Scheme) f (Y.affineCover.f i)) := inferInstance
  exact topologicalKrullDim_le_of_isIntegralHom_of_isAffine (pullback.snd f (Y.affineCover.f i))

/-- **A surjective integral morphism of schemes preserves the dimension.** This applies to finite
surjective morphisms, for example isogenies of abelian varieties. -/
theorem topologicalKrullDim_eq_of_isIntegralHom_of_surjective {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegralHom f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_isIntegralHom f)
    (topologicalKrullDim_le_of_specializingMap f f.continuous f.isClosedMap.specializingMap
      f.surjective)

/-- **A finite surjective morphism of schemes preserves the dimension.** -/
theorem topologicalKrullDim_eq_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  topologicalKrullDim_eq_of_isIntegralHom_of_surjective f

end ZInQ.Contrib.Dim
