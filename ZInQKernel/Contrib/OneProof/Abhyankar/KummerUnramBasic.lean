import ZInQKernel.Contrib.OneProof.Abhyankar.Assembly
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBase
import ZInQKernel.Contrib.OneProof.Abhyankar.EtaleBranch

/-!
# abhyankar: helpers for `KummerUnram`

* `height_under_eq_one` — height-one primes contract to height-one primes along an integral torsion-free
  extension of an integrally closed noetherian domain (going down);
* `dvr_atPrime` — the localization of a noetherian integrally closed domain at a height-one prime is a DVR;
* `unramifiedAt_of_local` — a prime `Q` of the integral closure `S'` of `B` in `Ω` is unramified over `B` as
  soon as the integral closure of the DVR `B_{Q ∩ B}` in `Ω` is unramified over it (`TsKummer.fu_of_unram`).
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem height_under_eq_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] [IsDomain S] [IsNoetherianRing S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] (Q : Ideal S) [Q.IsPrime] (hQ : Q.height = 1) : (Q.under R).height = 1 := by
  haveI : Q.LiesOver (Q.under R) := ⟨rfl⟩
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
  have hne : Q.under R ≠ ⊥ := Ideal.under_ne_bot R (Ideal.ne_bot_of_height_eq_one hQ)
  have hpos : (Q.under R).height ≠ 0 := fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  rw [hQ] at h1
  have hle : (Q.under R).height ≤ 1 := by rw [h1]; exact le_self_add
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hpos)

theorem dvr_atPrime {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (P : Ideal B) [P.IsPrime] (h : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have hdim : ringKrullDim (Localization.AtPrime P) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, h]
    rfl
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime P) := fun hF => by
    have := ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at this
    exact absurd this (by decide)
  haveI : Ring.DimensionLEOne (Localization.AtPrime P) := ⟨fun {q} hq0 hq => by
    by_contra hmax
    have hlt : q < maximalIdeal (Localization.AtPrime P) :=
      lt_of_le_of_ne (le_maximalIdeal hq.ne_top) (fun h' => hmax (h' ▸ maximalIdeal.isMaximal _))
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hq1 : q.height ≠ 0 := fun h0 => hq0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
    have hm := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Localization.AtPrime P)
    rw [hdim] at hm
    have hm' : (maximalIdeal (Localization.AtPrime P)).height = 1 := by exact_mod_cast hm
    rw [hm'] at h1
    have := ENat.one_le_iff_ne_zero.mpr hq1
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add this le_rfl) h1
    exact absurd h2 (by decide)⟩
  haveI : IsDedekindDomain (Localization.AtPrime P) := {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 3 1).mp
    (inferInstance : IsDedekindDomain (Localization.AtPrime P))

theorem unramifiedAt_of_local {A₀ K₀ B Ω : Type} [CommRing A₀] [IsDomain A₀] [Field K₀]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Field Ω] [Algebra A₀ B] [Algebra B Ω] [Algebra A₀ Ω] [Algebra K₀ Ω]
    [IsScalarTower A₀ B Ω] [IsScalarTower A₀ K₀ Ω] [FiniteDimensional K₀ Ω] [Algebra.IsSeparable K₀ Ω]
    (hBΩ : Function.Injective (algebraMap B Ω))
    (Q : Ideal (integralClosure B Ω)) [Q.IsPrime] (hP : (Q.under B).height = 1)
    (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra B T]
    [IsLocalization.AtPrime T (Q.under B)] [Algebra T Ω] [IsScalarTower B T Ω]
    (h : ∀ (Q' : Ideal (integralClosure T Ω)) [Q'.IsPrime]
      [Q'.LiesOver (maximalIdeal T)],
      Q'.ramificationIdx T = 1 ∧
      Algebra.IsSeparable (T ⧸ maximalIdeal T)
        (integralClosure T Ω ⧸ Q')) :
    Algebra.IsUnramifiedAt B Q := by
  classical
  have hTΩ : Function.Injective (algebraMap T Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.under B).primeCompl x
    have h1 : algebraMap T Ω
        (IsLocalization.mk' T b s) *
        algebraMap B Ω s = algebraMap B Ω b := by
      rw [IsScalarTower.algebraMap_apply B T Ω s,
        IsScalarTower.algebraMap_apply B T Ω b, ← map_mul,
        IsLocalization.mk'_spec]
    simp only at hx
    rw [hx, zero_mul] at h1
    have hb : b = 0 := hBΩ (by rw [← h1, map_zero])
    simp [hb]
  haveI : FaithfulSMul T Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hTΩ
  -- the fraction field of `T`
  letI : Algebra (FractionRing T) Ω :=
    FractionRing.liftAlgebra T Ω
  haveI : IsScalarTower T
      (FractionRing T) Ω :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have hA₀Ω : Function.Injective (algebraMap A₀ Ω) := by
    rw [IsScalarTower.algebraMap_eq A₀ K₀ Ω]
    exact (algebraMap K₀ Ω).injective.comp (IsFractionRing.injective A₀ K₀)
  have hcomp : ∀ z : A₀, algebraMap (FractionRing T) Ω
      (((algebraMap T (FractionRing T)).comp
      ((algebraMap B T).comp (algebraMap A₀ B))) z) =
      algebraMap A₀ Ω z := by
    intro z
    show algebraMap (FractionRing T) Ω
      (algebraMap T (FractionRing T)
        (algebraMap B T (algebraMap A₀ B z))) = _
    rw [← IsScalarTower.algebraMap_apply T
      (FractionRing T) Ω,
      ← IsScalarTower.algebraMap_apply B T Ω,
      ← IsScalarTower.algebraMap_apply A₀ B Ω]
  have hinjK' : Function.Injective ((algebraMap T
      (FractionRing T)).comp
      ((algebraMap B T).comp (algebraMap A₀ B))) := by
    intro x y hxy
    apply hA₀Ω
    have := congrArg (algebraMap (FractionRing T) Ω) hxy
    rwa [hcomp, hcomp] at this
  letI : Algebra K₀ (FractionRing T) :=
    (IsFractionRing.lift hinjK').toAlgebra
  haveI : IsScalarTower K₀ (FractionRing T) Ω :=
    IsScalarTower.of_algebraMap_eq' (by
      apply IsLocalization.ringHom_ext (nonZeroDivisors A₀)
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply A₀ K₀ Ω]
      show algebraMap A₀ Ω a = algebraMap _ Ω (IsFractionRing.lift hinjK' (algebraMap A₀ K₀ a))
      rw [IsFractionRing.lift_algebraMap, hcomp])
  haveI : FiniteDimensional (FractionRing T) Ω :=
    Module.Finite.of_restrictScalars_finite K₀ _ Ω
  haveI : Algebra.IsSeparable (FractionRing T) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K₀ _ Ω
  haveI hfu : Algebra.FormallyUnramified T
      (integralClosure T Ω) :=
    TsKummer.fu_of_unram T
      (FractionRing T) Ω h
  -- `integralClosure T Ω` is the localization of `S'` at `B ∖ P`
  have hP0 : ∀ x ∈ (Q.under B).primeCompl, algebraMap B Ω x ≠ 0 := fun x hx h0 =>
    hx (by rw [hBΩ (h0.trans (map_zero _).symm)]; exact Ideal.zero_mem _)
  letI : Algebra (integralClosure B Ω) (integralClosure T Ω) := (TsKummer.intClIncl B T Ω).toAlgebra
  obtain ⟨hst1, hst2, hloc⟩ := TsKummer.intCl_isLocalization B T Ω (Q.under B).primeCompl hP0
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (integralClosure B Ω) (Q.under B).primeCompl :
      Submonoid (integralClosure B Ω)) : Set (integralClosure B Ω)) (Q : Set (integralClosure B Ω)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hbQ
    exact hb hbQ
  haveI hQ'p : (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q inferInstance hdisj
  have hc : (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω))).comap
      (algebraMap (integralClosure B Ω) (integralClosure T Ω)) = Q :=
    IsLocalization.comap_map_of_isPrime_disjoint _ _ inferInstance hdisj
  haveI : IsLocalization.AtPrime
      (Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω)))) Q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (integralClosure B Ω) (Q.under B).primeCompl)
      (Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω))))
      (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω)))
    unfold IsLocalization.AtPrime at this ⊢
    convert this using 2
    exact hc.symm
  let e : Localization.AtPrime Q ≃ₐ[integralClosure B Ω]
      Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω))) :=
    IsLocalization.algEquiv Q.primeCompl _ _
  haveI : Algebra.FormallyUnramified B T :=
    Algebra.FormallyUnramified.of_isLocalization (Q.under B).primeCompl
  haveI : Algebra.FormallyUnramified B (integralClosure T Ω) :=
    Algebra.FormallyUnramified.comp B T (integralClosure T Ω)
  haveI : Algebra.FormallyUnramified (integralClosure T Ω)
      (Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω)))) :=
    Algebra.FormallyUnramified.of_isLocalization
      (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω))).primeCompl
  haveI : Algebra.FormallyUnramified B
      (Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω)))) :=
    Algebra.FormallyUnramified.comp B (integralClosure T Ω) _
  haveI : IsScalarTower B (integralClosure B Ω)
      (Localization.AtPrime (Q.map (algebraMap (integralClosure B Ω) (integralClosure T Ω)))) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply B (integralClosure T Ω),
        IsScalarTower.algebraMap_apply (integralClosure B Ω) (integralClosure T Ω),
        IsScalarTower.algebraMap_apply B (integralClosure B Ω) (integralClosure T Ω)])
  exact Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars B)

end Abhyankar
