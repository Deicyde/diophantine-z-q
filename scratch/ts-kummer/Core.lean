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

/-! ## Verbatim copies (dev only) -/

/-! ## Part 1: the function-field objects (genuine Mathlib definitions) -/

/-- The affine coordinate ring at `∞` of `P¹_ℚ`: a copy of `ℚ[s]`, mapped to `ℚ(X)` by
`s ↦ X⁻¹` (`Algebra InfCoord (RatFunc ℚ)` below). -/
def InfCoord : Type := Polynomial ℚ

noncomputable instance : CommRing InfCoord := inferInstanceAs (CommRing ℚ[X])

noncomputable instance : Algebra InfCoord (RatFunc ℚ) :=
  @RingHom.toAlgebra InfCoord (RatFunc ℚ) _ _
    (Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹) : ℚ[X] →+* RatFunc ℚ)

/-- The local coordinate `s = 1/X` at `∞`, as an element of `InfCoord`. -/
noncomputable def infUnif : InfCoord := (Polynomial.X : ℚ[X])

/-- `ℚ[s] → E` through `ℚ(X)` (`s ↦ X⁻¹`). -/
@[reducible] noncomputable def infAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E] : Algebra InfCoord E :=
  ((algebraMap (RatFunc ℚ) E).comp (algebraMap InfCoord (RatFunc ℚ))).toAlgebra

/-- `ℤ[X] → E` through `ℚ[X]` (coefficients `ℤ ⊆ ℚ`). -/
@[reducible] noncomputable def intPolyAlg (E : Type) [Field E] [Algebra ℚ[X] E] : Algebra ℤ[X] E :=
  ((algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).toAlgebra



/-- **`E'` is the compositum `E(s)` along `X ↦ r(s)`**: a field embedding `ι : E → E'` sending the
coordinate `X` of `ℚ(X) ⊆ E` to `r ∈ ℚ(s) ⊆ E'` (`s` the coordinate of the second `RatFunc ℚ`),
with `E'` generated as a field by `ι(E)` and `s`. -/
def KummerShape (E E' : Type) [Field E] [Field E'] [Algebra (RatFunc ℚ) E]
    [Algebra (RatFunc ℚ) E'] (ι : E →+* E') (r : RatFunc ℚ) : Prop :=
  ι (algebraMap (RatFunc ℚ) E RatFunc.X) = algebraMap (RatFunc ℚ) E' r ∧
    Subfield.closure (Set.range ι ∪ {algebraMap (RatFunc ℚ) E' RatFunc.X}) = ⊤

/-- The Kummer substitution at a finite branch point: `X = b + s^n / c`, i.e. `s^n = c (X − b)`. -/
def rFin (b c : ℚ) (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C (b * c) + X ^ n) / algebraMap ℚ[X] (RatFunc ℚ) (C c)

/-- The Kummer substitution at `∞`: `X = c / s^n`, i.e. `s^n = c / X`. -/
def rInf (c : ℚ) (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C c) / algebraMap ℚ[X] (RatFunc ℚ) (X ^ n)

/-- **Glue from T2 (Abhyankar's lemma), finite branch point.** If `E' = E(s)` with
`s^n = c (X − b)` (`c ≠ 0`) and every prime of `B` over `X − b` has ramification index dividing
`n`, then `E'/ℚ(s)` is unramified over `s = 0`. Proof: T2 (`PkgI2.AbhyankarDVR`) for the DVR
`ℚ[X]_(X−b)` with uniformizer `c (X − b) = s^n` gives `e = n` over `X = b` for every prime of
`E'`; `ℚ(s)/ℚ(X)` is totally ramified of index `n` at `s = 0`, and `e` is multiplicative in
towers. -/
def KummerAbhyankarFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rFin b c n) →
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = Ideal.span {X - C b} →
      Q.ramificationIdx ℚ[X] ∣ n) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.under ℚ[X] = Ideal.span {X} →
      Q'.ramificationIdx ℚ[X] = 1

/-- `KummerAbhyankarFin` is glue whose proof uses the bundle leaf T2. -/
def KummerAbhyankarFinGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerAbhyankarFin

/-! ### The case at `∞` -/

/-- **Glue from T2 (Abhyankar's lemma), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`
(`c ≠ 0`) and every prime of the integral closure of `ℚ[1/X]` in `E` over `1/X` has ramification
index dividing `n`, then `E'/ℚ(s)` is unramified over `s = 0`. Proof: T2 for the DVR
`ℚ[1/X]_(1/X)` with uniformizer `c · (1/X) = s^n`, and multiplicativity of `e`. -/
def KummerAbhyankarInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rInf c n) →
    (letI := infAlg E
      ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime →
        Q.under InfCoord = Ideal.span {infUnif} → Q.ramificationIdx InfCoord ∣ n) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.under ℚ[X] = Ideal.span {X} →
      Q'.ramificationIdx ℚ[X] = 1

/-- `KummerAbhyankarInf` is glue whose proof uses the bundle leaf T2. -/
def KummerAbhyankarInfGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerAbhyankarInf


end TsKummer

namespace TsKummer

/-- `ℚ[X] → E'` through `ℚ(s)` is injective. -/
theorem polyMap_injective (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] : Function.Injective (algebraMap ℚ[X] E') := by
  rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E']
  exact (algebraMap (RatFunc ℚ) E').injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))

/-- `KummerShape` gives `E' = E(s)` as an intermediate-field statement. -/
theorem adjoin_eq_top_of_shape {E E' : Type} [Field E] [Field E'] [Algebra (RatFunc ℚ) E]
    [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E'] [IsScalarTower ℚ[X] (RatFunc ℚ) E']
    (ι : E →+* E') (r : RatFunc ℚ) (h : KummerShape E E' ι r) :
    letI := ι.toAlgebra
    IntermediateField.adjoin E {algebraMap ℚ[X] E' X} = ⊤ := by
  letI := ι.toAlgebra
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield,
    IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X]
  exact h.2

/-- An integral element for `σ` makes the whole polynomial ring integral (if `σ` fixes constants). -/
theorem isIntegral_of_X (σ : ℚ[X] →+* ℚ[X]) (hC : ∀ a : ℚ, σ (C a) = C a)
    (hX : σ.IsIntegralElem X) : σ.IsIntegral := by
  intro f
  induction f using Polynomial.induction_on with
  | C a => rw [← hC a]; exact σ.isIntegralElem_map
  | add f g hf hg => exact RingHom.IsIntegralElem.add σ hf hg
  | monomial k a _ =>
    rw [pow_succ, ← mul_assoc]
    exact RingHom.IsIntegralElem.mul σ (by assumption) hX

/-- **`KummerAbhyankarFinGlue` is proved** (from T2, via `abhyankar_core`). -/
theorem kummerAbhyankarFinGlue : KummerAbhyankarFinGlue := by
  intro t2 E _ _ _ _ _ E' _ _ _ _ _ ι b c n hn hc hshape hE Q' hQ'p hQ'
  have hcu : IsUnit (C c : ℚ[X]) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
  let σ : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)
  have hσC : ∀ a : ℚ, σ (C a) = C a := fun a => by simp [σ]
  have hσX : σ X = C b + C c⁻¹ * X ^ n := by simp [σ]
  have hsn : σ (C c * (X - C b)) = X ^ n := by
    rw [map_mul, map_sub, hσC, hσC, hσX, add_sub_cancel_left, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * (X - C b)), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hσ : ∀ x, algebraMap ℚ[X] E' (σ x) = ι (algebraMap ℚ[X] E x) := by
    have : (algebraMap ℚ[X] E').comp σ = ι.comp (algebraMap ℚ[X] E) := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap ℚ[X] E').comp σ).comp C)
          ((ι.comp (algebraMap ℚ[X] E)).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        rw [hσX, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X, hshape.1]
        congr 1
        rw [rFin, eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
          (C_ne_zero.mpr hc)), ← map_mul]
        congr 1
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        rw [C_mul]
        linear_combination (X ^ n) * h1
    intro x
    exact congrArg (fun g => g x) this
  haveI : (Ideal.span {C c * (X - C b)} : Ideal ℚ[X]).IsPrime := by
    rw [Ideal.span_singleton_mul_left_unit hcu]
    exact (Ideal.span_singleton_prime (X_sub_C_ne_zero b)).mpr (prime_X_sub_C b)
  haveI : (Ideal.span {X} : Ideal ℚ[X]).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  refine abhyankar_core t2 ℚ[X] (RatFunc ℚ) E E' ℚ[X] ι σ hσ (isIntegral_of_X σ hσC hXint)
    (polyMap_injective E') (C c * (X - C b)) (mul_ne_zero (C_ne_zero.mpr hc) (X_sub_C_ne_zero b))
    X X_ne_zero n hn hsn (adjoin_eq_top_of_shape ι _ hshape) ?_ Q' hQ'
  intro Q hQ hQu
  rw [Ideal.span_singleton_mul_left_unit hcu] at hQu
  exact hE Q hQ hQu

theorem eval₂_X_eq (f : ℚ[X]) :
    eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X f = algebraMap ℚ[X] (RatFunc ℚ) f := by
  have := eval₂_algebraMap_X f (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))
  simpa [RatFunc.algebraMap_X] using this

/-- `ℚ(X)` is the fraction field of `InfCoord = ℚ[1/X]`. -/
theorem isFractionRing_infCoord : IsFractionRing InfCoord (RatFunc ℚ) := by
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have key : ∀ (f : ℚ[X]) (N : ℕ), f.natDegree ≤ N →
      eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N f) * RatFunc.X ^ N =
        algebraMap ℚ[X] (RatFunc ℚ) f := by
    intro f N hf
    letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
    have := eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X N f hf
    rw [invOf_eq_inv, eval₂_X_eq] at this
    exact this
  have hinj0 : ∀ f : ℚ[X], eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ f = 0 → f = 0 := by
    intro f hf
    letI : Invertible (RatFunc.X⁻¹ : RatFunc ℚ) := invertibleOfNonzero (inv_ne_zero hX)
    have h := eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (f : ℚ[X]).natDegree
      (f : ℚ[X]) le_rfl
    rw [hf, invOf_eq_inv, inv_inv, eval₂_X_eq] at h
    have h2 := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hX))
    rw [map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ)), reflect_eq_zero_iff] at h2
    exact h2
  have hinj : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    exact hinj0 f hf
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))
  · intro z
    obtain ⟨P, Q, hQ, rfl⟩ : ∃ P Q : ℚ[X], Q ≠ 0 ∧
        z = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q :=
      ⟨z.num, z.denom, z.denom_ne_zero, (RatFunc.num_div_denom z).symm⟩
    set N := max P.natDegree Q.natDegree
    have hQN : (reflect N Q : InfCoord) ∈ nonZeroDivisors InfCoord :=
      mem_nonZeroDivisors_of_ne_zero (M₀ := InfCoord)
        (show (reflect N Q : InfCoord) ≠ 0 from fun h => hQ (reflect_eq_zero_iff.mp h))
    refine ⟨⟨reflect N P, ⟨reflect N Q, hQN⟩⟩, ?_⟩
    change algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q *
        eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N Q) =
      eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N P)
    have hP := key P N (le_max_left _ _)
    have hQ' := key Q N (le_max_right _ _)
    have hQ0 : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr hQ
    have hXN : (RatFunc.X : RatFunc ℚ) ^ N ≠ 0 := pow_ne_zero _ hX
    have hq : eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N Q) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hQ'; exact hQ0 hQ'.symm
    rw [← hP, ← hQ', mul_div_mul_right _ _ hXN, div_mul_cancel₀ _ hq]
  · intro x y h
    exact ⟨1, by simp [hinj h]⟩

/-- **`KummerAbhyankarInfGlue` is proved** (from T2, via `abhyankar_core` with `R0 = ℚ[1/X]`). -/
theorem kummerAbhyankarInfGlue : KummerAbhyankarInfGlue := by
  intro t2 E _ _ _ _ _ E' _ _ _ _ _ ι c n hn hc hshape hE Q' hQ'p hQ'
  letI := infAlg E
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  letI : IsDedekindDomain InfCoord := inferInstanceAs (IsDedekindDomain ℚ[X])
  letI : Algebra ℚ InfCoord := inferInstanceAs (Algebra ℚ ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  have hcu : IsUnit (C c : ℚ[X]) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  let σ : InfCoord →+* ℚ[X] := σ0
  have hσC : ∀ a : ℚ, σ0 (C a) = C a := fun a => by simp [σ0]
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
  have hsn : σ0 (C c * X) = X ^ n := by
    rw [map_mul, hσC, hσX, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ0.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * X), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hσ : ∀ x : InfCoord, algebraMap ℚ[X] E' (σ x) = ι (algebraMap InfCoord E x) := by
    have : ((algebraMap ℚ[X] E').comp σ0 : ℚ[X] →+* E') =
        (ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E') := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap ℚ[X] E').comp σ0).comp C)
          (((ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E')).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        rw [hσX]
        change algebraMap ℚ[X] E' (C c⁻¹ * X ^ n) =
          ι (algebraMap (RatFunc ℚ) E (eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ X))
        rw [eval₂_X, map_inv₀ (algebraMap (RatFunc ℚ) E), map_inv₀ ι, hshape.1,
          ← map_inv₀ (algebraMap (RatFunc ℚ) E'),
          IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E']
        congr 1
        have hCc : algebraMap ℚ[X] (RatFunc ℚ) (C c) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (C_ne_zero.mpr hc)
        rw [rInf, inv_div, eq_div_iff hCc, ← map_mul]
        congr 1
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        linear_combination (X ^ n) * h1
    intro x
    exact congrArg (fun g => g x) this
  let π0 : InfCoord := (C c * X : ℚ[X])
  haveI : (Ideal.span {π0}).IsPrime := by
    change (Ideal.span {(C c * X : ℚ[X])} : Ideal ℚ[X]).IsPrime
    rw [Ideal.span_singleton_mul_left_unit hcu]
    exact (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  haveI : (Ideal.span {X} : Ideal ℚ[X]).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  refine abhyankar_core t2 InfCoord (RatFunc ℚ) E E' ℚ[X] ι σ hσ
    (isIntegral_of_X σ0 hσC hXint) (polyMap_injective E') π0
    (show (C c * X : ℚ[X]) ≠ 0 from mul_ne_zero (C_ne_zero.mpr hc) X_ne_zero) X X_ne_zero n hn hsn
    (adjoin_eq_top_of_shape ι _ hshape) ?_ Q' hQ'
  intro Q hQ hQu
  have hspan : (Ideal.span {π0}) = Ideal.span {infUnif} := by
    change (Ideal.span {(C c * X : ℚ[X])} : Ideal ℚ[X]) = Ideal.span {X}
    rw [Ideal.span_singleton_mul_left_unit hcu]
  rw [hspan] at hQu
  exact hE Q hQ hQu

end TsKummer

namespace TsKummer

/-- **Glue (STANDARD): a compositum of unramified extensions is unramified (DVR form).**
`R` a discrete valuation ring with fraction field `K`; `L/K`, `L'/K` finite separable; `M` a field
containing `L` and `L'` over `K` and generated by them (`M = L·L'`). If every prime of the integral
closure of `R` in `L`, and in `L'`, over the maximal ideal of `R` has ramification index `1` and
separable residue field extension, then so does every such prime of the integral closure of `R`
in `M`. (Stated in the binder conventions of T2 `PkgI2.AbhyankarDVR`. Reference: base change and
composition of étale algebras, SGA 1 Exp. I, Prop. 4.6 and Cor. 4.8 (numbers UNVERIFIED); for
function fields Stichtenoth, *Algebraic function fields and codes*, Prop. 3.9.6 (UNVERIFIED).) -/
def UnramCompositum : Prop :=
  ∀ (R K L L' M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field L'] [Algebra K L'] [Algebra R L'] [IsScalarTower R K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L']
    [Field M] [Algebra L M] [Algebra L' M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower K L' M] [IsScalarTower R K M],
    IntermediateField.adjoin L (Set.range (algebraMap L' M)) = ⊤ →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q)) →
    (∀ (Q : Ideal (integralClosure R L')) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L' ⧸ Q)) →
    ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q)

/-- Localization transfer, downwards: a prime of the integral closure of `R0_p` in `F` over the
maximal ideal comes from a prime of the integral closure of `R0` over `p`, with the same `e`. -/
theorem locTransfer_down (R0 F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [Algebra (Localization.AtPrime p) F]
    [IsScalarTower R0 (Localization.AtPrime p) F] (hinj : Function.Injective (algebraMap R0 F))
    (Q : Ideal (integralClosure (Localization.AtPrime p) F)) [Q.IsPrime]
    [Q.LiesOver (maximalIdeal (Localization.AtPrime p))] :
    letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
    ∃ P0 : Ideal (integralClosure R0 F), P0.IsPrime ∧ P0.under R0 = p ∧
      Q.ramificationIdx (Localization.AtPrime p) = P0.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 (Localization.AtPrime p) F p.primeCompl hP
  letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
  set P0 := Q.comap (algebraMap (integralClosure R0 F) (integralClosure (Localization.AtPrime p) F))
  haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p (Localization.AtPrime p) Q
  haveI : P0.IsPrime := Ideal.IsPrime.comap _
  have hQ : Q = P0.map (algebraMap (integralClosure R0 F) (integralClosure (Localization.AtPrime p) F)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 F) p.primeCompl)
      (integralClosure (Localization.AtPrime p) F) Q).symm
  refine ⟨P0, inferInstance, (Ideal.LiesOver.over (P := P0) (p := p)).symm, ?_⟩
  rw [hQ]
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p _ _ P0

/-- Localization transfer, upwards. -/
theorem locTransfer_up (R0 F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [Algebra (Localization.AtPrime p) F]
    [IsScalarTower R0 (Localization.AtPrime p) F] (hinj : Function.Injective (algebraMap R0 F))
    (P : Ideal (integralClosure R0 F)) [P.IsPrime] [P.LiesOver p] :
    letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
    ∃ Q : Ideal (integralClosure (Localization.AtPrime p) F), Q.IsPrime ∧
      Q.LiesOver (maximalIdeal (Localization.AtPrime p)) ∧
      Q.ramificationIdx (Localization.AtPrime p) = P.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 (Localization.AtPrime p) F p.primeCompl hP
  letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
  exact ⟨_, IsLocalization.AtPrime.isPrime_map_of_liesOver _ p _ P,
    IsLocalization.AtPrime.liesOver_map_of_liesOver p _ _ P,
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p _ _ P⟩

/-- In residue characteristic `0`, residue field extensions over a `ℚ`-algebra are separable. -/
theorem isSeparable_residue_of_rat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R] (m : Ideal R) [m.IsMaximal] (Q : Ideal S) [Q.IsMaximal] [Q.LiesOver m]
    [Algebra.IsIntegral R S] :
    letI : Field (R ⧸ m) := Ideal.Quotient.field _
    letI : Field (S ⧸ Q) := Ideal.Quotient.field _
    Algebra.IsSeparable (R ⧸ m) (S ⧸ Q) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field _
  letI : Field (S ⧸ Q) := Ideal.Quotient.field _
  haveI : CharZero (R ⧸ m) := by
    have : Function.Injective ((Ideal.Quotient.mk m).comp (algebraMap ℚ R)) := RingHom.injective _
    exact charZero_of_injective_ringHom this
  haveI : Algebra.IsIntegral (R ⧸ m) (S ⧸ Q) := inferInstance
  infer_instance

/-- **Abstract compositum transfer (residue characteristic 0).** As `abhyankar_core`, with the
Kummer step replaced by an extension `A/R0` (finite via `σ`) unramified over `p`: if every prime of
the integral closure of `R0` in `L` over `p`, and every prime of `A` over `p`, has ramification
index `1`, then every prime of the integral closure of `A` in `M = L·Frac(A)` over a prime of `A`
over `p` has ramification index `1` over `A`. -/
theorem compositum_core0 (hU : UnramCompositum)
    (R0 K L M A : Type) [CommRing R0] [IsDomain R0] [IsDedekindDomain R0] [Algebra ℚ R0]
    [Field K] [Algebra R0 K] [IsFractionRing R0 K]
    [Field L] [Algebra K L] [Algebra R0 L] [IsScalarTower R0 K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Field M] [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A M]
    (ι : L →+* M) (σ : R0 →+* A) (hσ : ∀ x, algebraMap A M (σ x) = ι (algebraMap R0 L x))
    (hfin : letI := σ.toAlgebra; Module.Finite R0 A) (hσinj : Function.Injective σ)
    (hAM : Function.Injective (algebraMap A M))
    (p : Ideal R0) [hpp : p.IsPrime] (hp0 : p ≠ ⊥)
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L (Set.range (algebraMap A M)) = ⊤)
    (hE : ∀ Q : Ideal (integralClosure R0 L), Q.IsPrime → Q.under R0 = p →
      Q.ramificationIdx R0 = 1)
    (hA : ∀ g : Ideal A, g.IsPrime → g.comap σ = p → letI := σ.toAlgebra;
      g.ramificationIdx R0 = 1)
    (Q' : Ideal (integralClosure A M)) [hQ'p : Q'.IsPrime] (hQ' : (Q'.under A).comap σ = p) :
    Q'.ramificationIdx A = 1 := by
  classical
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
  haveI : Module.Finite R0 A := hfin
  haveI : Algebra.IsIntegral R0 A := inferInstance
  haveI hpmax : p.IsMaximal := Ideal.IsPrime.isMaximal hpp hp0
  have hR0K : Function.Injective (algebraMap R0 K) := IsFractionRing.injective R0 K
  haveI : CharZero K := charZero_of_injective_ringHom
    (show Function.Injective ((algebraMap R0 K).comp (algebraMap ℚ R0)) from RingHom.injective _)
  -- the fraction field `K'` of `A`
  set K' := FractionRing A
  have hR0K' : Function.Injective (algebraMap R0 K') := by
    rw [IsScalarTower.algebraMap_eq R0 A K']
    exact (IsFractionRing.injective A K').comp hσinj
  letI : Algebra K K' := (IsFractionRing.lift hR0K' : K →+* K').toAlgebra
  haveI : IsScalarTower R0 K K' := IsScalarTower.of_algebraMap_eq
    (fun x => (IsFractionRing.lift_algebraMap hR0K' x).symm)
  haveI : Module.IsTorsionFree R0 A := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hσinj
  haveI : FaithfulSMul R0 K' := (faithfulSMul_iff_algebraMap_injective R0 K').mpr hR0K'
  haveI : FiniteDimensional K K' := by
    letI := FractionRing.liftAlgebra R0 K'
    haveI : IsScalarTower R0 (FractionRing R0) K' := FractionRing.isScalarTower_liftAlgebra R0 K'
    haveI : FiniteDimensional (FractionRing R0) K' := by
      haveI : FiniteDimensional (FractionRing R0) (FractionRing A) := inferInstance
      exact this
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv R0 K).toRingEquiv
      (RingEquiv.refl K') ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors R0)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply R0 K K', ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable K K' := inferInstance
  letI : Algebra K' M := (IsFractionRing.lift hAM : K' →+* M).toAlgebra
  haveI : IsScalarTower A K' M := IsScalarTower.of_algebraMap_eq
    (fun x => (IsFractionRing.lift_algebraMap hAM x).symm)
  haveI : IsScalarTower K K' M := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors R0)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R0 K M, ← IsScalarTower.algebraMap_apply R0 K K',
      IsScalarTower.algebraMap_apply R0 A K', ← IsScalarTower.algebraMap_apply A K' M,
      ← IsScalarTower.algebraMap_apply R0 A M]
  -- the DVR `Rp`
  set Rp := Localization.AtPrime p
  haveI hDVR : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R0 hp0 Rp
  letI : Algebra Rp K := IsLocalization.localizationAlgebraOfSubmonoidLe Rp K p.primeCompl
    (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R0 Rp K := IsLocalization.localization_isScalarTower_of_submonoid_le Rp K
    p.primeCompl (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
  letI : Algebra Rp L := ((algebraMap K L).comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp K' := ((algebraMap K K').comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp M := ((algebraMap K M).comp (algebraMap Rp K)).toAlgebra
  haveI : IsScalarTower Rp K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K M := IsScalarTower.of_algebraMap_eq' rfl
  have tow : ∀ (F : Type) [Field F] [Algebra K F] [Algebra R0 F] [IsScalarTower R0 K F],
      letI : Algebra Rp F := ((algebraMap K F).comp (algebraMap Rp K)).toAlgebra
      IsScalarTower R0 Rp F := by
    intro F _ _ _ _
    letI : Algebra Rp F := ((algebraMap K F).comp (algebraMap Rp K)).toAlgebra
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R0 F x = algebraMap K F (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K, ← IsScalarTower.algebraMap_apply R0 K F]
  haveI : IsScalarTower R0 Rp L := tow L
  haveI : IsScalarTower R0 Rp K' := tow K'
  haveI : IsScalarTower R0 Rp M := tow M
  have hR0L : Function.Injective (algebraMap R0 L) := by
    rw [IsScalarTower.algebraMap_eq R0 K L]; exact (algebraMap K L).injective.comp hR0K
  have hR0M : Function.Injective (algebraMap R0 M) := by
    rw [IsScalarTower.algebraMap_eq R0 K M]; exact (algebraMap K M).injective.comp hR0K
  -- hypotheses of `UnramCompositum`
  have hadj' : IntermediateField.adjoin L (Set.range (algebraMap K' M)) = ⊤ := by
    refine eq_top_iff.mpr (hadj.symm.le.trans (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap A K' a, (IsScalarTower.algebraMap_apply A K' M a).symm⟩
  have hypL : ∀ (Q : Ideal (integralClosure Rp L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      Q.ramificationIdx Rp = 1 ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp L ⧸ Q) := by
    intro Q _ _
    obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down R0 L p hR0L Q
    refine ⟨he.trans (hE P0 hP0 hP0u), ?_⟩
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
      (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
    letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
    exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
  have hypL' : ∀ (Q : Ideal (integralClosure Rp K')) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      Q.ramificationIdx Rp = 1 ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp K' ⧸ Q) := by
    intro Q _ _
    obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down R0 K' p hR0K' Q
    refine ⟨?_, ?_⟩
    · rw [he]
      let e : integralClosure R0 K' ≃ₐ[R0] A :=
        IsIntegralClosure.equiv R0 (integralClosure R0 K') K' A
      rw [← ramificationIdx_map_algEquiv e P0]
      apply hA _ (Ideal.map_isPrime_of_equiv e)
      change Ideal.comap (algebraMap R0 A) (P0.map e) = p
      rw [← hP0u, Ideal.under]
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap, ← e.commutes x, ← Ideal.mem_comap,
        Ideal.comap_map_of_bijective e e.bijective]
    · haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
        (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
      letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
      exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
  have key := hU Rp K L K' M hadj' hypL hypL'
  -- back to `integralClosure A M`
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
  haveI : Q'.LiesOver p := ⟨by rw [← Ideal.under_under (B := A) Q']; exact hQ'.symm⟩
  set P := Q'.map f with hP_def
  haveI : P.IsPrime := Ideal.map_isPrime_of_equiv f
  have hPunder : P.under R0 = p := by
    ext x
    rw [Ideal.under, Ideal.mem_comap, hP_def, ← f.commutes x, ← Ideal.mem_comap,
      Ideal.comap_map_of_bijective f f.bijective, ← Ideal.mem_comap]
    change x ∈ Q'.under R0 ↔ x ∈ p
    rw [← Ideal.LiesOver.over (P := Q') (p := p)]
  haveI : P.LiesOver p := ⟨hPunder.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up R0 M p hR0M P
  have h1 := (key Qp).1
  rw [hQpe, hP_def, ramificationIdx_map_algEquiv f Q'] at h1
  haveI : Module.IsTorsionFree A (integralClosure A M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply hAM
    have := congrArg Subtype.val hxy
    simpa using this
  haveI : Q'.LiesOver (Q'.under A) := ⟨rfl⟩
  have htow := Ideal.ramificationIdx_tower (R := R0) (Q'.under A) Q'
  rw [h1] at htow
  exact Nat.eq_one_of_mul_eq_one_left htow.symm

end TsKummer
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.compositum_core0
