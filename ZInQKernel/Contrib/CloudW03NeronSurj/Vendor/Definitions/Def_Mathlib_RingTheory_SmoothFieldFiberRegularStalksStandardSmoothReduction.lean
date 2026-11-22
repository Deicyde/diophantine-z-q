/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 1 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 82 line(s) of `#print axioms` / `#guard_msgs` audit removed (diagnostics only; no proof term).
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

universe u

theorem kmf2_fiber_isLocalization_primeCompl_congr {A : Type*} [CommRing A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization I.primeCompl S] :
    IsLocalization J.primeCompl S := by
  subst h
  exact ‹IsLocalization I.primeCompl S›

theorem kmf2_fiber_input_of_standardSmooth_case
    (hss : ∀ (k B : Type u) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q)) :
    SmoothFieldFiberRegularStalksInput.{u} := by
  intro k A _ _ _ hsm p hp
  haveI : Algebra.Smooth k A := hsm

  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k p

  have hdisj : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  haveI hq : (p.map (algebraMap A (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p hp hdisj
  have hcomap : (p.map (algebraMap A (Localization.Away f))).comap
      (algebraMap A (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdisj

  haveI : IsRegularLocalRing
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f)))) :=
    hss k (Localization.Away f) hstd (p.map (algebraMap A (Localization.Away f)))

  haveI : IsLocalization p.primeCompl
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f)))) :=
    kmf2_fiber_isLocalization_primeCompl_congr hcomap _
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime p)
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f))))).symm.toRingEquiv)

theorem kmf2_fiber_standardSmooth_case_of_input
    (hinput : SmoothFieldFiberRegularStalksInput.{u})
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (hstd : Algebra.IsStandardSmooth k B) (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hstd
  exact hinput k B inferInstance q

theorem kmf2_fiber_input_iff_standardSmooth_case :
    SmoothFieldFiberRegularStalksInput.{u} ↔
      ∀ (k B : Type u) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q) :=
  ⟨fun h k B _ _ _ hstd q _ => kmf2_fiber_standardSmooth_case_of_input h k B hstd q,
   kmf2_fiber_input_of_standardSmooth_case⟩

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing
    (A : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : IsDedekindDomain A := inferInstance
  haveI : IsRegularRing A := inferInstance
  exact IsRegularRing.isRegularLocalRing_localization p

theorem kmf2_fiber_isRegularRing_polynomial (k : Type*) [Field k] :
    IsRegularRing (Polynomial k) := by
  haveI : IsDedekindDomain (Polynomial k) := inferInstance
  infer_instance

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial
    (k : Type*) [Field k] (p : Ideal (Polynomial k)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing
    (Polynomial k) p

theorem kmf2_fiber_sat_smooth_polynomial (k : Type*) [Field k] :
    Algebra.Smooth k (Polynomial k) :=
  { formallySmooth := inferInstance, finitePresentation := inferInstance }

theorem kmf2_fiber_gate_input_clause_polynomial (k : Type*) [Field k] :
    Algebra.Smooth k (Polynomial k) ∧
      ∀ (p : Ideal (Polynomial k)) [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p) := by
  refine ⟨kmf2_fiber_sat_smooth_polynomial k, ?_⟩
  intro p hp
  exact kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial k p

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isReduced_of_mem_minimalPrimes
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : IsNoetherianRing (Localization.AtPrime p) := inferInstance
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
  haveI : IsArtinianRing (Localization.AtPrime p) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  haveI : IsReduced (Localization.AtPrime p) := inferInstance
  exact SmoothFieldFiberRegularStalks.isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem kmf2_fiber_falsif_not_standardSmooth_case_dropping_standardSmooth :
    ¬ (∀ (k B : Type) [Field k] [CommRing B] [Algebra k B] (q : Ideal B) [q.IsPrime],
        IsRegularLocalRing (Localization.AtPrime q)) :=
  SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth

theorem kmf2_fiber_not_isStandardSmooth_dualNumber_of_standardSmooth_case
    (hss : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q)) :
    ¬ Algebra.IsStandardSmooth ℚ (DualNumber ℚ) := fun h =>
  SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber ℚ
    (hss ℚ (DualNumber ℚ) h (IsLocalRing.maximalIdeal (DualNumber ℚ)))

end ZInQ.Contrib.CloudW03NeronSurj.FLT
