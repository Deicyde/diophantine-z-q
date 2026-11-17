/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
Native height-one localization determination of regular principal ideals.
SOURCE ONLY / UNCOMPILED, original universe u. No valuation/normal/Picard,
factorization or local-equality Factory is supplied. Reduced fractions are
actual native maps, and the prime-localization comparison is an actual
R-algebra isomorphism with its original coefficient map.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Ideal.RegularPrincipal
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe u

open scoped nonZeroDivisors

namespace H5OriginalDVR.Lane5.I0Native

/-- In a native Noetherian UFD, all height-one local divisibilities detect
actual global divisibility. The original s/r are not replaced. -/
theorem dvd_of_height_one_localizations
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (s r : R) (hs : s ≠ 0)
    (hloc : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      algebraMap R (Localization.AtPrime p.asIdeal) s ∣
        algebraMap R (Localization.AtPrime p.asIdeal) r) : s ∣ r := by
  let Q := FractionRing R
  let q : Q := IsLocalization.mk' Q r ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩
  obtain ⟨n, d, hred, heq⟩ := IsFractionRing.exists_reduced_fraction R q
  have hnd : n * s = r * (d : R) := by
    apply IsFractionRing.injective R Q
    have hn : q * algebraMap R Q (d : R) = algebraMap R Q n := by
      simpa only [heq] using IsLocalization.mk'_spec Q n d
    have hr : q * algebraMap R Q s = algebraMap R Q r :=
      IsLocalization.mk'_spec Q r ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩
    simp only [map_mul]
    calc algebraMap R Q n * algebraMap R Q s
        = (q * algebraMap R Q (d : R)) * algebraMap R Q s := by rw [hn]
      _ = (q * algebraMap R Q s) * algebraMap R Q (d : R) := by ring
      _ = algebraMap R Q r * algebraMap R Q (d : R) := by rw [hr]
  have hdu : IsUnit (d : R) := by
    by_contra hdnu
    obtain ⟨π, hπirr, hπd⟩ := WfDvdMonoid.exists_irreducible_factor
      hdnu (nonZeroDivisors.ne_zero d.property)
    have hπ : Prime π := hπirr.prime
    let P : Ideal R := Ideal.span {π}
    letI : P.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
    have hPh : P.height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) hπ.not_isUnit
    let S := Localization.AtPrime P
    obtain ⟨c, hc⟩ := hloc (⟨P, inferInstance⟩ : PrimeSpectrum R) hPh
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj P.primeCompl c
    have hrt : r * (t : R) = s * a := by
      apply IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
      simp only [map_mul]
      calc algebraMap R S r * algebraMap R S (t : R)
          = (algebraMap R S s * c) * algebraMap R S (t : R) := by rw [hc]
        _ = algebraMap R S s * (c * algebraMap R S (t : R)) := by ring
        _ = algebraMap R S s * algebraMap R S a := by rw [ht]
    have hnt : n * (t : R) = a * (d : R) := by
      apply mul_left_cancel₀ hs
      calc s * (n * (t : R)) = (n * s) * (t : R) := by ring
        _ = (r * (d : R)) * (t : R) := by rw [hnd]
        _ = (r * (t : R)) * (d : R) := by ring
        _ = (s * a) * (d : R) := by rw [hrt]
        _ = s * (a * (d : R)) := by ring
    have hπnt : π ∣ n * (t : R) := by rw [hnt]; exact hπd.mul_left a
    obtain hπn | hπt := hπ.dvd_or_dvd hπnt
    · exact hπ.not_isUnit (hred hπn hπd)
    · exact t.property (Ideal.mem_span_singleton.mpr hπt)
  apply hdu.dvd_mul_left.mp
  exact ⟨n, by rw [mul_comm (d : R) r, ← hnd, mul_comm n s]⟩

/-- Both regular-principal ideal generators are detected at height-one
primes; no comparison of supports or divisor multiplicities is substituted. -/
theorem regular_principal_eq_of_height_one_localizations
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I J : Ideal R)
    (hI : I.IsRegularPrincipal) (hJ : J.IsRegularPrincipal)
    (hloc : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) =
        J.map (algebraMap R (Localization.AtPrime p.asIdeal))) : I = J := by
  obtain ⟨f, hf, hIf⟩ := hI
  obtain ⟨g, hg, hJg⟩ := hJ
  have hgf : g ∣ f := dvd_of_height_one_localizations R g f
      (nonZeroDivisors.ne_zero hg) (fun p hp => by
    have hm : algebraMap R (Localization.AtPrime p.asIdeal) f ∈
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) :=
      Ideal.mem_map_of_mem _ (by rw [hIf]; exact Ideal.mem_span_singleton_self f)
    rw [hloc p hp, hJg, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
    exact hm)
  have hfg : f ∣ g := dvd_of_height_one_localizations R f g
      (nonZeroDivisors.ne_zero hf) (fun p hp => by
    have hm : algebraMap R (Localization.AtPrime p.asIdeal) g ∈
        J.map (algebraMap R (Localization.AtPrime p.asIdeal)) :=
      Ideal.mem_map_of_mem _ (by rw [hJg]; exact Ideal.mem_span_singleton_self g)
    rw [← hloc p hp, hIf, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
    exact hm)
  rw [hIf, hJg]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hgf)
    (Ideal.span_singleton_le_span_singleton.mpr hfg)

/-- The original affine-ring height-one maps determine their images at
an ACTUAL UFD stalk. Nested prime localizations use the original R-map. -/
theorem localized_regular_principal_eq_of_height_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    [IsNoetherianRing S] [IsDomain S] [UniqueFactorizationMonoid S]
    (I J : Ideal R)
    (hI : (I.map (algebraMap R S)).IsRegularPrincipal)
    (hJ : (J.map (algebraMap R S)).IsRegularPrincipal)
    (hloc : ∀ q : PrimeSpectrum R, q.asIdeal.height = 1 →
      I.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
        J.map (algebraMap R (Localization.AtPrime q.asIdeal))) :
    I.map (algebraMap R S) = J.map (algebraMap R S) := by
  apply regular_principal_eq_of_height_one_localizations S
    (I.map (algebraMap R S)) (J.map (algebraMap R S)) hI hJ
  intro q hqh
  let T := Localization.AtPrime q.asIdeal
  letI : Algebra R T := inferInstance
  letI : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := T) fun _ => rfl
  let q₀ : Ideal R := q.asIdeal.comap (algebraMap R S)
  letI : q₀.IsPrime := inferInstance
  letI : IsLocalization.AtPrime T q₀ :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      p.primeCompl T q.asIdeal
  have hq₀h : q₀.height = 1 :=
    (IsLocalization.height_under p.primeCompl q.asIdeal).trans hqh
  let e : Localization.AtPrime q₀ ≃ₐ[R] T :=
    IsLocalization.algEquiv q₀.primeCompl (Localization.AtPrime q₀) T
  have hcomp : e.toRingEquiv.toRingHom.comp (algebraMap R (Localization.AtPrime q₀)) =
      algebraMap R T := RingHom.ext fun r => e.commutes r
  have heqT : I.map (algebraMap R T) = J.map (algebraMap R T) := by
    have hh := congrArg (Ideal.map e.toRingEquiv.toRingHom)
      (hloc (⟨q₀, inferInstance⟩ : PrimeSpectrum R) hq₀h)
    simpa only [Ideal.map_map, hcomp] using hh
  rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq R S T]
  exact heqT

end H5OriginalDVR.Lane5.I0Native
