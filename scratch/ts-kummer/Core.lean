import ZInQKernel.HDecomp.Objects
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Flat.TorsionFree

/-! ts-kummer development file: the abstract Abhyankar transfer (`abhyankar_core`), from T2. -/

open Polynomial IsLocalRing

set_option linter.style.haveILetI false

noncomputable section

namespace TsKummer

/-- The ramification index is invariant under an `R`-algebra isomorphism. -/
theorem ramificationIdx_map_algEquiv {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S ≃ₐ[R] S') (q : Ideal S) [hq : q.IsPrime] :
    (q.map f).ramificationIdx R = q.ramificationIdx R := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hbij : Function.Bijective (algebraMap S S') := f.bijective
  let e : S' ≃ₗ[S] S :=
    { toFun := f.symm
      invFun := f
      map_add' := fun x y => map_add f.symm x y
      map_smul' := fun r x => by
        change f.symm (f r * x) = r * f.symm x
        simp
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  haveI : Module.Flat S S' := Module.Flat.of_linearEquiv e
  have hq' : (q.map f).IsPrime := Ideal.map_isPrime_of_equiv f
  have hunder : (q.map f).under S = q := by
    change Ideal.comap (algebraMap S S') (Ideal.map (algebraMap S S') q) = q
    exact Ideal.comap_map_of_bijective _ hbij
  haveI : (q.map f).LiesOver q := ⟨hunder.symm⟩
  rw [Ideal.ramificationIdx_tower q (q.map f)]
  suffices h : (q.map f).ramificationIdx S = 1 by rw [h, mul_one]
  let Sq := Localization.AtPrime (q.map f)
  rw [Ideal.ramificationIdx_def, hunder, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, IsScalarTower.algebraMap_eq S S' Sq, ← Ideal.map_map]
  change Ideal.map (algebraMap S' Sq) (Ideal.map (algebraMap S S') q) = _
  exact Localization.AtPrime.map_eq_maximalIdeal

/-- The inclusion of integral closures `integralClosure R0 L → integralClosure Rp L`. -/
def intClIncl (R0 Rp L : Type) [CommRing R0] [CommRing Rp] [Field L] [Algebra R0 Rp]
    [Algebra R0 L] [Algebra Rp L] [IsScalarTower R0 Rp L] :
    integralClosure R0 L →+* integralClosure Rp L where
  toFun c := ⟨c.1, IsIntegral.tower_top (A := Rp) c.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A field is its own localization at any submonoid of nonzero elements. -/
theorem isLocalization_field_self {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

theorem intCl_isLocalization (R0 Rp L : Type) [CommRing R0] [CommRing Rp] [Field L]
    [Algebra R0 Rp] [Algebra R0 L] [Algebra Rp L] [IsScalarTower R0 Rp L] (P : Submonoid R0)
    [IsLocalization P Rp] (hP : ∀ x ∈ P, algebraMap R0 L x ≠ 0) :
    letI := (intClIncl R0 Rp L).toAlgebra
    IsScalarTower (integralClosure R0 L) (integralClosure Rp L) L ∧
    IsScalarTower R0 (integralClosure R0 L) (integralClosure Rp L) ∧
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R0 L) P)
      (integralClosure Rp L) := by
  letI := (intClIncl R0 Rp L).toAlgebra
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid L P) L := isLocalization_field_self _ hP
  have h1 : IsScalarTower (integralClosure R0 L) (integralClosure Rp L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h2 : IsScalarTower R0 (integralClosure R0 L) (integralClosure Rp L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  exact ⟨h1, h2, IsLocalization.integralClosure P⟩

/-- **Abstract Abhyankar transfer from T2.** `R0` a Dedekind `ℚ`-algebra with fraction field `K`,
`L/K` finite separable, `ι : L → M` a field embedding, `A` a Dedekind domain with `A → M`
injective, and `σ : R0 → A` integral with `A → M` compatible with `ι` on `R0`. If `π0` generates a
nonzero prime of `R0`, `σ π0 = s ^ n` with `(s)` prime, `M = L(s)`, and every prime of the integral
closure of `R0` in `L` over `(π0)` has ramification index dividing `n`, then every prime of the
integral closure of `A` in `M` over `(s)` is unramified over `A`. -/
theorem abhyankar_core (t2 : PkgI2.AbhyankarDVR.{0})
    (R0 K L M A : Type) [CommRing R0] [IsDomain R0] [IsDedekindDomain R0] [Algebra ℚ R0]
    [Field K] [Algebra R0 K] [IsFractionRing R0 K]
    [Field L] [Algebra K L] [Algebra R0 L] [IsScalarTower R0 K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Field M] [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A M]
    (ι : L →+* M) (σ : R0 →+* A) (hσ : ∀ x, algebraMap A M (σ x) = ι (algebraMap R0 L x))
    (hint : σ.IsIntegral) (hAM : Function.Injective (algebraMap A M))
    (π0 : R0) [hπp : (Ideal.span {π0}).IsPrime] (hπ0 : π0 ≠ 0)
    (s : A) [hsp : (Ideal.span {s}).IsPrime] (hs0 : s ≠ 0) (n : ℕ) (hn : 0 < n)
    (hsn : σ π0 = s ^ n)
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L {algebraMap A M s} = ⊤)
    (hE : ∀ Q : Ideal (integralClosure R0 L), Q.IsPrime → Q.under R0 = Ideal.span {π0} →
      Q.ramificationIdx R0 ∣ n)
    (Q' : Ideal (integralClosure A M)) [hQ'p : Q'.IsPrime] (hQ' : Q'.under A = Ideal.span {s}) :
    Q'.ramificationIdx A = 1 := by
  classical
  set p : Ideal R0 := Ideal.span {π0} with hp_def
  letI : Algebra R0 A := σ.toAlgebra
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  letI : Algebra R0 M := ((algebraMap K M).comp (algebraMap R0 K)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 A M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ι (algebraMap K L (algebraMap R0 K x)) = algebraMap A M (σ x)
    rw [hσ, IsScalarTower.algebraMap_apply R0 K L]
  haveI : Algebra.IsIntegral R0 A := ⟨hint⟩
  have hp0 : p ≠ ⊥ := by
    rw [hp_def, Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  haveI hpmax : p.IsMaximal := Ideal.IsPrime.isMaximal hπp hp0
  -- the DVR `Rp`
  set Rp := Localization.AtPrime p
  haveI hDVR : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R0 hp0 Rp
  letI : Algebra Rp K := IsLocalization.localizationAlgebraOfSubmonoidLe Rp K p.primeCompl (nonZeroDivisors R0)
    p.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R0 Rp K := IsLocalization.localization_isScalarTower_of_submonoid_le Rp K p.primeCompl
    (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
  letI : Algebra Rp L := ((algebraMap K L).comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp M := ((algebraMap K M).comp (algebraMap Rp K)).toAlgebra
  haveI : IsScalarTower Rp K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 Rp L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R0 L x = algebraMap K L (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K, ← IsScalarTower.algebraMap_apply R0 K L]
  haveI : IsScalarTower R0 Rp M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap K M (algebraMap R0 K x) = algebraMap K M (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K]
  -- injectivity of `R0 → L`, `R0 → M`
  have hR0K : Function.Injective (algebraMap R0 K) := IsFractionRing.injective R0 K
  have hR0L : Function.Injective (algebraMap R0 L) := by
    rw [IsScalarTower.algebraMap_eq R0 K L]
    exact (algebraMap K L).injective.comp hR0K
  have hR0M : Function.Injective (algebraMap R0 M) := by
    rw [IsScalarTower.algebraMap_eq R0 K M]
    exact (algebraMap K M).injective.comp hR0K
  have hPL : ∀ x ∈ p.primeCompl, algebraMap R0 L x ≠ 0 := fun x hx h0 =>
    hx (by rw [hR0L (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  have hPM : ∀ x ∈ p.primeCompl, algebraMap R0 M x ≠ 0 := fun x hx h0 =>
    hx (by rw [hR0M (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  -- the uniformizer
  have hmax : maximalIdeal Rp = Ideal.span {algebraMap R0 Rp π0} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])
  have hirr : Irreducible (algebraMap R0 Rp π0) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  -- units
  have hunit : ∀ k : ℕ, k ≠ 0 → IsUnit (k : Rp) := by
    intro k hk
    have h1 : IsUnit ((algebraMap R0 Rp).comp (algebraMap ℚ R0) (k : ℚ)) :=
      (Ne.isUnit (by exact_mod_cast hk : (k : ℚ) ≠ 0)).map _
    simpa using h1
  -- localizing the integral closure of `R0` in `L`
  obtain ⟨hL1, hL2, hL3⟩ := intCl_isLocalization R0 Rp L p.primeCompl hPL
  letI := (intClIncl R0 Rp L).toAlgebra
  -- T2's hypothesis
  have hyp : ∀ (Q : Ideal (integralClosure Rp L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      IsUnit ((Q.ramificationIdx Rp : ℕ) : Rp) ∧ Q.ramificationIdx Rp ∣ n ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp L ⧸ Q) := by
    intro Q _ _
    set P0 := Q.comap (algebraMap (integralClosure R0 L) (integralClosure Rp L))
    haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rp Q
    haveI : P0.IsPrime := Ideal.IsPrime.comap _
    have hQ : Q = P0.map (algebraMap (integralClosure R0 L) (integralClosure Rp L)) :=
      (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 L) p.primeCompl)
        (integralClosure Rp L) Q).symm
    have he : Q.ramificationIdx Rp = P0.ramificationIdx R0 := by
      rw [hQ]
      exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp
        (integralClosure Rp L) P0
    have hdvd : Q.ramificationIdx Rp ∣ n := by
      rw [he]; exact hE P0 inferInstance (Ideal.LiesOver.over (P := P0) (p := p)).symm
    refine ⟨hunit _ (fun h0 => by rw [h0, zero_dvd_iff] at hdvd; omega), hdvd, ?_⟩
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
      (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
    letI : Field (Rp ⧸ maximalIdeal Rp) := Ideal.Quotient.field _
    letI : Field (integralClosure Rp L ⧸ Q) := Ideal.Quotient.field _
    haveI : CharZero (Rp ⧸ maximalIdeal Rp) := by
      have : Function.Injective
          ((Ideal.Quotient.mk (maximalIdeal Rp)).comp ((algebraMap R0 Rp).comp (algebraMap ℚ R0))) :=
        RingHom.injective _
      exact charZero_of_injective_ringHom this
    haveI : Algebra.IsIntegral (Rp ⧸ maximalIdeal Rp) (integralClosure Rp L ⧸ Q) :=
      inferInstance
    infer_instance
  -- T2 applied to `M = L(s)`
  have ht : (algebraMap A M s) ^ n = algebraMap Rp M (algebraMap R0 Rp π0) := by
    rw [← IsScalarTower.algebraMap_apply R0 Rp M, IsScalarTower.algebraMap_apply R0 A M, ← map_pow]
    congr 1
    exact hsn.symm
  have key := t2 Rp K L M (algebraMap R0 Rp π0) hirr n hn (hunit n (by omega)) hyp
    (algebraMap A M s) ht hadj
  -- localizing the integral closure of `R0` in `M`
  obtain ⟨hM1, hM2, hM3⟩ := intCl_isLocalization R0 Rp M p.primeCompl hPM
  letI := (intClIncl R0 Rp M).toAlgebra
  -- `integralClosure A M = integralClosure R0 M`
  have hmem : ∀ x : M, IsIntegral A x ↔ IsIntegral R0 x := fun x =>
    ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩
  let f0 : integralClosure A M ≃+* integralClosure R0 M :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (hmem y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let f : integralClosure A M ≃ₐ[R0] integralClosure R0 M :=
    AlgEquiv.ofRingEquiv (f := f0) (fun r => rfl)
  -- `(s) ∩ R0 = p`
  have hsunder : (Ideal.span {s}).comap (algebraMap R0 A) = p := by
    have hle : p ≤ (Ideal.span {s}).comap (algebraMap R0 A) := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      change σ π0 ∈ Ideal.span {s}
      rw [hsn]; exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self s) n hn
    exact (hpmax.eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm
  haveI : (Ideal.span {s}).LiesOver p := ⟨hsunder.symm⟩
  haveI : Q'.LiesOver (Ideal.span {s}) := ⟨hQ'.symm⟩
  haveI : Q'.LiesOver p := Ideal.LiesOver.trans Q' (Ideal.span {s}) p
  set P := Q'.map f with hP_def
  haveI : P.IsPrime := Ideal.map_isPrime_of_equiv f
  have hPunder : P.under R0 = p := by
    ext x
    rw [Ideal.under, Ideal.mem_comap, hP_def, ← f.commutes x, ← Ideal.mem_comap,
      Ideal.comap_map_of_bijective f f.bijective, ← Ideal.mem_comap]
    change x ∈ Q'.under R0 ↔ x ∈ p
    rw [← Ideal.LiesOver.over (P := Q') (p := p)]
  haveI : P.LiesOver p := ⟨hPunder.symm⟩
  haveI := IsLocalization.AtPrime.isPrime_map_of_liesOver (integralClosure R0 M) p
    (integralClosure Rp M) P
  haveI := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rp (integralClosure Rp M) P
  have h1 := (key (P.map (algebraMap (integralClosure R0 M) (integralClosure Rp M)))).1
  rw [IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp (integralClosure Rp M) P,
    hP_def, ramificationIdx_map_algEquiv f Q'] at h1
  -- the tower `R0 → A → integralClosure A M`
  haveI : Module.IsTorsionFree A (integralClosure A M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply hAM
    have := congrArg Subtype.val hxy
    simpa using this
  have htow := Ideal.ramificationIdx_tower (R := R0) (Ideal.span {s}) Q'
  have hsn' : (Ideal.span {s}).ramificationIdx R0 = n := by
    have hs_ne : Ideal.span {s} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hs0
    haveI : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {s})) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hs_ne _
    rw [Ideal.ramificationIdx_eq p (Ideal.span {s})]
    have hmapn : p.map (algebraMap R0 (Localization.AtPrime (Ideal.span {s}))) =
        maximalIdeal (Localization.AtPrime (Ideal.span {s})) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, Ideal.span_singleton_pow,
        Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        IsScalarTower.algebraMap_apply R0 A (Localization.AtPrime (Ideal.span {s}))]
      rw [show algebraMap R0 A π0 = s ^ n from hsn]
    rw [hmapn, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  rw [h1, hsn'] at htow
  have : n * Q'.ramificationIdx A = n * 1 := by rw [← htow, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hn this

end TsKummer
#print axioms TsKummer.abhyankar_core
