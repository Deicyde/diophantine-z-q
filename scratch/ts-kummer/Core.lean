import ZInQKernel.HDecomp.Objects
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! ts-kummer development file: the abstract Abhyankar transfer (`abhyankar_core`), from T2. -/

open Polynomial IsLocalRing
open scoped TensorProduct

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
theorem isLocalization_field_self' {A K : Type*} [CommRing A] [Field K] [Algebra A K]
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
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid L P) L := isLocalization_field_self' _ hP
  have h1 : IsScalarTower (integralClosure R0 L) (integralClosure Rp L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h2 : IsScalarTower R0 (integralClosure R0 L) (integralClosure Rp L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  exact ⟨h1, h2, IsLocalization.integralClosure P⟩

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
  haveI : Algebra.IsAlgebraic (R ⧸ m) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

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
    letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
    exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
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

/-- The prime `p·ℤ[X]` of `ℤ[X]`: the generic point of the fibre of `P¹_ℤ` at `p`. -/
def vertPrime (p : ℕ) : Ideal ℤ[X] := Ideal.map (C : ℤ →+* ℤ[X]) (Ideal.span {(p : ℤ)})

/-- **No vertical ramification at `p`** (Beckmann's hypothesis (d)): every prime of the integral
closure of `ℤ[X]` in `E` lying over `p·ℤ[X]` (the height-one primes of the fibre at `p`) has
ramification index `1`. Mathlib's `ramificationIdx` localizes at the prime, so this is the
ramification index of the discrete valuation ring at the generic point of a component of the
fibre at `p`. (With `[E : ℚ(X)] < p` the residue extensions are then separable: the inseparable
degree is a power of `p` dividing `f ≤ [E : ℚ(X)]`.) -/
def NoVerticalRam (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∀ Q : Ideal (integralClosure ℤ[X] E), Q.IsPrime → Q.under ℤ[X] = vertPrime p →
    Q.ramificationIdx ℤ[X] = 1

/-- **Glue (ramification in a compositum), finite branch point.** If `E' = E(s)` with
`s^n = c (X − b)`, `b ∈ S` and `E/ℚ(X)` is unramified over every finite prime other than the
`X − b'` (`b' ∈ S`), then a ramified prime of `E'/ℚ(s)` lies over `s = 0` or contains
`s^n − c (b' − b)` for some `b' ∈ S ∖ {b}`. Proof: over a prime `g` of `ℚ[s]` with
`g ∩ ℚ[X] = h`: if `h = (X − b)` then `g = (s)`; if `h = (X − b')` then `s^n − c(b' − b) ∈ g`;
otherwise `E` and `ℚ(s)` are both unramified over `h` (`ℚ(s)/ℚ(X)` ramifies only over `b` and
`∞`), hence so is the compositum. -/
def KummerOtherBranchFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rFin b c n) →
    ∀ S : Finset ℚ, b ∈ S →
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      (∀ b' ∈ S, Q.under ℚ[X] ≠ Ideal.span {X - C b'}) → Q.ramificationIdx ℚ[X] = 1) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.ramificationIdx ℚ[X] ≠ 1 →
      Q'.under ℚ[X] = Ideal.span {X} ∨
        ∃ b' ∈ S, b' ≠ b ∧ X ^ n - C (c * (b' - b)) ∈ Q'.under ℚ[X]

/-- **Glue (Gauss valuation), finite branch point.** If `E' = E(s)` with `s^n = c (X − b)`,
`0 < n < p`, `c` a `p`-unit, `b` `p`-integral, `[E : ℚ(X)] < p`, and `E` has no vertical
ramification at `p`, then neither has `E'`. Proof: the Gauss valuation of `ℚ(s)` restricts to the
Gauss valuation of `ℚ(X)` (the substitution `X ↦ b + s^n/c` is injective mod `p`), with `e = 1`
and residue extension `𝔽_p(s)/𝔽_p(X̄)` separable of degree `n < p`; the vertical primes of `E` are
unramified with separable residue fields (`[E : ℚ(X)] < p`); a compositum of extensions unramified
at a valuation is unramified there. -/
def KummerVerticalFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ) (p : ℕ), p.Prime → 0 < n → n < p →
    Module.finrank (RatFunc ℚ) E < p → c ≠ 0 → padicValRat p c = 0 → 0 ≤ padicValRat p b →
    KummerShape E E' ι (rFin b c n) → NoVerticalRam E p → NoVerticalRam E' p

/-- **Glue (ramification in a compositum), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`
and `E/ℚ(X)` is unramified over every finite prime other than the `X − b'` (`b' ∈ S`), then a
ramified prime of `E'/ℚ(s)` lies over `s = 0` or contains `b' s^n − c` for some `b' ∈ S ∖ {0}`.
Proof: `ℚ(s)/ℚ(X)` ramifies only over `X = ∞` (`s = 0`) and `X = 0` (`s = ∞`, not a prime of
`ℚ[s]`); over `s = α ≠ 0` the point `X = c/α^n` is finite and nonzero, and the compositum is
ramified there only if `E` is, i.e. `c/α^n = b' ∈ S`. -/
def KummerOtherBranchInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rInf c n) →
    ∀ S : Finset ℚ,
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      (∀ b' ∈ S, Q.under ℚ[X] ≠ Ideal.span {X - C b'}) → Q.ramificationIdx ℚ[X] = 1) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.ramificationIdx ℚ[X] ≠ 1 →
      Q'.under ℚ[X] = Ideal.span {X} ∨
        ∃ b' ∈ S, b' ≠ 0 ∧ C b' * X ^ n - C c ∈ Q'.under ℚ[X]

/-- **Glue (Gauss valuation), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`, `0 < n < p`,
`c` a `p`-unit, `[E : ℚ(X)] < p`, and `E` has no vertical ramification at `p`, then neither has
`E'`. Proof: for `f ∈ ℤ_(p)[X]` primitive of degree `d`, `s^{nd} f(c/s^n) ∈ ℤ_(p)[s]` is primitive
(the substitution is injective mod `p`), so the Gauss valuation of `ℚ(s)` restricts to that of
`ℚ(X)`, with `e = 1` and residue extension separable of degree `n < p`; then as in
`KummerVerticalFin`. -/
def KummerVerticalInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ) (p : ℕ), p.Prime → 0 < n → n < p →
    Module.finrank (RatFunc ℚ) E < p → c ≠ 0 → padicValRat p c = 0 →
    KummerShape E E' ι (rInf c n) → NoVerticalRam E p → NoVerticalRam E' p


/-- `ℤ[X] → E` through `ℚ[X]` (the map of `intPolyAlg`). -/
abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

/-- **The local base `ℤ[X]_m` mapped to `E`** (the localization of `zxMap E`; elements outside
`m` are nonzero, hence units in the field `E`). -/
@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- `ℚ(X)` is the fraction field of `ℤ[X]` (through `ℤ[X] → ℚ[X] → ℚ(X)`). -/
theorem isFractionRing_zx :
    letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := zxMap_injective (RatFunc ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero y (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨⟨P, Q⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℚ[X]) z
    obtain ⟨bP, hbPM, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
    obtain ⟨bQ, hbQM, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (Q : ℚ[X])
    set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
    set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q : ℚ[X])
    have hbP0 : bP ≠ 0 := nonZeroDivisors.ne_zero hbPM
    have hbQ0 : bQ ≠ 0 := nonZeroDivisors.ne_zero hbQM
    have hQ0 : (Q : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero Q
    have hmapQ : Q'.map (Int.castRingHom ℚ) = C (bQ : ℚ) * Q := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbQ
    have hmapP : P'.map (Int.castRingHom ℚ) = C (bP : ℚ) * P := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbP
    have hy : C bP * Q' ∈ nonZeroDivisors ℤ[X] := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      refine mul_ne_zero (by simpa using hbP0) ?_
      intro h0
      have := hmapQ
      rw [h0, Polynomial.map_zero] at this
      exact mul_ne_zero (by simpa using hbQ0) hQ0 this.symm
    refine ⟨⟨C bQ * P', ⟨_, hy⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_C, hmapP, hmapQ, map_mul, eq_intCast]
    rw [← hz]
    simp only [map_intCast, Int.cast_id, Polynomial.map_intCast]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

/-- A `p`-integral rational has denominator prime to `p`. -/
theorem not_dvd_den_of_nonneg (p : ℕ) [hp : Fact p.Prime] (s : ℚ) (hs : 0 ≤ padicValRat p s) :
    ¬ p ∣ s.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ s.num := by
    intro hn
    have h1 : p ∣ s.num.natAbs := Int.natCast_dvd.mp hn
    exact hp.out.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 s.reduced).eq_one_of_dvd hd)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at hs
  have := one_le_padicValNat_of_dvd s.den_nz hd
  omega

theorem vertPrime_isPrime (p : ℕ) (hp : p.Prime) : (vertPrime p).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).mpr
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp))

/-- **An extension of degree `< p` in characteristic `p` is separable.** -/
theorem isSeparable_of_finrank_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h : Module.finrank K L < p) : Algebra.IsSeparable K L := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  have hirr := minpoly.irreducible hint
  rcases separable_or p hirr with hs | ⟨-, g, hg, hgf⟩
  · exact hs
  · exfalso
    have hdeg := minpoly.natDegree_le (A := K) (B := L) x
    have h1 : (minpoly K x).natDegree = g.natDegree * p := by rw [← hgf, natDegree_expand]
    have hg1 : 1 ≤ g.natDegree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have := natDegree_eq_zero.mp h0
      obtain ⟨c, rfl⟩ := this
      exact hg.not_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
        rintro rfl
        simp at hg)))
    have : p ≤ (minpoly K x).natDegree := by rw [h1]; nlinarith
    omega

abbrev Qbar := AlgebraicClosure ℚ

/-- **Glue (algebra; STANDARD): the compositum exists, with a prime over a given prime.** Let
`E/ℚ(X)` be finite and `r = P/Q ∈ ℚ(s)` non-constant, regular at `s₀ ∈ ℚ` with `r(s₀) = t`. For
every prime `𝔓` of the integral closure `B` of `ℚ[X]` in `E` over `X − t` and every embedding
`φ : B/𝔓 → ℚ̄` there are a field `E'` finite over `ℚ(s)` which is a compositum `E(s)` along
`X ↦ r` (a factor of `E ⊗_{ℚ(X)} ℚ(s)`), so `[E' : ℚ(s)] ≤ [E : ℚ(X)]`, a prime `𝔓'` of the
integral closure of `ℚ[s]` in `E'` over `s − s₀`, and an embedding `φ'` of its residue field with
`ℚ(φ(B/𝔓)) ⊆ ℚ(φ'(B'/𝔓'))`. Proof: every valuation of `E` over `X = t` extends to some factor
of `E ⊗ ℚ(s)` above the valuation `s = s₀` of `ℚ(s)` (which restricts to `X = t` on `ℚ(X)`), and
`φ` extends to the finite extension of residue fields as `ℚ̄` is algebraically closed. -/
def KummerCompositum : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (P Q : ℚ[X]) (t s₀ : ℚ), Q.eval s₀ ≠ 0 → P.eval s₀ = t * Q.eval s₀ → (∀ a : ℚ, P ≠ C a * Q) →
    ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime → 𝔓.under ℚ[X] = Ideal.span {X - C t} →
    ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
    ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
      (ι : E →+* E'),
      KummerShape E E' ι (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) ∧
      Module.finrank (RatFunc ℚ) E' ≤ Module.finrank (RatFunc ℚ) E ∧
      ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
        𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
        ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
          IntermediateField.adjoin ℚ (Set.range φ) ≤ IntermediateField.adjoin ℚ (Set.range φ')

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

/-- A copy of `ℚ[X]` used as the source of a substitution `X ↦ r` (so that its module structure
on the target `ℚ[X]` is the one induced by the substitution). -/
def SrcPoly : Type := Polynomial ℚ

instance : CommRing SrcPoly := inferInstanceAs (CommRing ℚ[X])
instance : IsDomain SrcPoly := inferInstanceAs (IsDomain ℚ[X])
instance : IsPrincipalIdealRing SrcPoly := inferInstanceAs (IsPrincipalIdealRing ℚ[X])
instance : IsDedekindDomain SrcPoly := inferInstanceAs (IsDedekindDomain ℚ[X])
instance : Algebra ℚ SrcPoly := inferInstanceAs (Algebra ℚ ℚ[X])

/-- The identity `SrcPoly → ℚ[X]`. -/
def SrcPoly.toPoly (f : SrcPoly) : ℚ[X] := f

/-- Substitution `X ↦ r` (`r` non-constant) is unramified at every nonzero prime `g` of the target
`ℚ[X]` not containing `r'`. -/
theorem polyUnram (r : ℚ[X]) (hr : 0 < r.natDegree)
    (hint : (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).IsIntegral)
    (g : Ideal ℚ[X]) [hg : g.IsPrime] (hg0 : g ≠ ⊥) (hder : derivative r ∉ g) :
    letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
    g.ramificationIdx SrcPoly = 1 := by
  letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
  have hσ : ∀ f : SrcPoly, algebraMap SrcPoly ℚ[X] f = f.toPoly.comp r := fun f => rfl
  have hinj : Function.Injective (algebraMap SrcPoly ℚ[X]) := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.toPoly.comp r = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso; rw [hr', natDegree_C] at hr; exact lt_irrefl 0 hr
  haveI : Module.IsTorsionFree SrcPoly ℚ[X] :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
  set h := g.under SrcPoly with hh_def
  have hh0 : h ≠ ⊥ := Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  obtain ⟨q, rfl⟩ := Submodule.IsPrincipal.principal g
  obtain ⟨f, hf⟩ := Submodule.IsPrincipal.principal h
  have hq0 : q ≠ 0 := fun h0 => hg0 (by rw [h0]; exact Submodule.span_singleton_eq_bot.mpr rfl)
  have hqp : Prime q := (Ideal.span_singleton_prime hq0).mp hg
  have hf0 : f ≠ 0 := fun h0 => hh0 (by rw [hf, h0]; exact Submodule.span_singleton_eq_bot.mpr rfl)
  haveI hhp : h.IsPrime := Ideal.IsPrime.under _ _
  have hfp : Prime f := by
    have : (Ideal.span {f} : Ideal SrcPoly).IsPrime := by
      have e : (Ideal.span {f} : Ideal SrcPoly) = h := hf.symm
      rw [e]; exact hhp
    exact (Ideal.span_singleton_prime hf0).mp this
  have hfp' : Prime f.toPoly := hfp
  haveI : (Ideal.span {q}).LiesOver h := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx h (Ideal.span {q}) hh0]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]; exact Ideal.map_comap_le
  · have hfmem : f ∈ h := by rw [hf]; exact Submodule.mem_span_singleton_self f
    have hFq : q ∣ f.toPoly.comp r := by
      rw [← Ideal.mem_span_singleton, ← hσ]; exact hfmem
    have hmap : h.map (algebraMap SrcPoly ℚ[X]) = Ideal.span {f.toPoly.comp r} := by
      have e : h = Ideal.span {f} := hf
      rw [e, Ideal.map_span, Set.image_singleton, hσ]
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    intro hdvd
    have h2 : q ∣ derivative (f.toPoly.comp r) := by
      simpa using pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rw [derivative_comp] at h2
    rcases hqp.dvd_or_dvd h2 with h3 | h3
    · exact hder (Ideal.mem_span_singleton.mpr h3)
    · obtain ⟨u, v, huv⟩ := (hfp'.irreducible.separable : f.toPoly.Separable)
      have := congrArg (fun t => t.comp r) huv
      simp only [add_comp, mul_comp, one_comp] at this
      have h4 : q ∣ 1 := by
        rw [← this]
        exact dvd_add (dvd_mul_of_dvd_right hFq _) (dvd_mul_of_dvd_right h3 _)
      exact hqp.not_unit (isUnit_of_dvd_one h4)

/-- An integral substitution `X ↦ r` makes `ℚ[X]` module-finite over the source. -/
theorem finite_of_isIntegral (r : ℚ[X])
    (hint : (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).IsIntegral) :
    letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
    Module.Finite SrcPoly ℚ[X] := by
  letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
  haveI : IsScalarTower ℚ SrcPoly ℚ[X] := IsScalarTower.of_algebraMap_eq (fun a => by
    change C a = (C a).comp r
    rw [C_comp])
  haveI : Algebra.FiniteType SrcPoly ℚ[X] :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := ℚ) (S := SrcPoly) (A := ℚ[X])
  haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
  exact Algebra.IsIntegral.finite

/-- Compatibility of the finite Kummer substitution with `ι` (from `KummerShape`). -/
theorem finSubst_compat {E E' : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] (ι : E →+* E') (b c : ℚ) (n : ℕ) (hc : c ≠ 0)
    (hshape : KummerShape E E' ι (rFin b c n)) (x : ℚ[X]) :
    algebraMap ℚ[X] E' (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n) x) =
      ι (algebraMap ℚ[X] E x) := by
  have : (algebraMap ℚ[X] E').comp (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)) =
      ι.comp (algebraMap ℚ[X] E) := by
    apply Polynomial.ringHom_ext
    · intro a
      have := RingHom.ext_rat
        (((algebraMap ℚ[X] E').comp (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n))).comp C)
        ((ι.comp (algebraMap ℚ[X] E)).comp C)
      exact congrArg (fun g => g a) this
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X, hshape.1]
      congr 1
      rw [rFin, eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (C_ne_zero.mpr hc)), ← map_mul]
      congr 1
      have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
      rw [C_mul]
      linear_combination (X ^ n) * h1
  exact congrArg (fun g => g x) this

/-- A prime of `ℚ[X]` containing an irreducible `f` is `(f)`. -/
theorem eq_span_of_irreducible_mem {f : ℚ[X]} (hf : Irreducible f) (g : Ideal ℚ[X])
    [hg : g.IsPrime] (hX : f ∈ g) : g = Ideal.span {f} := by
  have hmax : (Ideal.span {f} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hf
  exact (hmax.eq_of_le hg.ne_top (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))).symm

/-- `X` is the only prime of `ℚ[X]` containing `X`. -/
theorem eq_span_X_of_mem (g : Ideal ℚ[X]) [hg : g.IsPrime] (hX : X ∈ g) : g = Ideal.span {X} :=
  eq_span_of_irreducible_mem irreducible_X g hX

/-- `r' = C (c⁻¹ n) X^(n-1)` lies outside every prime not containing `X`. -/
theorem derivative_notMem (a c : ℚ) (n : ℕ) (hn : 0 < n) (hc : c ≠ 0) (g : Ideal ℚ[X])
    [hg : g.IsPrime] (hX : X ∉ g) : derivative (C a + C c⁻¹ * X ^ n) ∉ g := by
  rw [derivative_add, derivative_C, zero_add, derivative_C_mul_X_pow]
  intro hm
  rcases hg.mem_or_mem hm with h1 | h1
  · refine hg.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_C.mpr (Ne.isUnit ?_)))
    exact mul_ne_zero (inv_ne_zero hc) (by exact_mod_cast hn.ne')
  · exact hX (hg.mem_of_pow_mem _ h1)

/-- **`KummerOtherBranchFin` from `UnramCompositum`.** -/
theorem kummerOtherBranchFin_of_unram (hU : UnramCompositum) : KummerOtherBranchFin := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι b c n hn hc hshape S hbS hE Q' hQ'p hQ'e
  classical
  let σ : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)
  have hσC : ∀ a : ℚ, σ (C a) = C a := fun a => by simp [σ]
  have hσX : σ X = C b + C c⁻¹ * X ^ n := by simp [σ]
  have hsn : σ (C c * (X - C b)) = X ^ n := by
    rw [map_mul, map_sub, hσC, hσC, hσX, add_sub_cancel_left, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * (X - C b)), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hint : σ.IsIntegral := isIntegral_of_X σ hσC hXint
  have hrdeg : 0 < (C b + C c⁻¹ * X ^ n : ℚ[X]).natDegree := by
    rw [natDegree_C_add, natDegree_C_mul_X_pow n _ (inv_ne_zero hc)]; exact hn
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.comp (C b + C c⁻¹ * X ^ n) = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso
      have := congrArg natDegree hr'
      rw [natDegree_C] at this; omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hS'⟩ := hcon
  apply hQ'e
  set g := Q'.under ℚ[X] with hg_def
  haveI hgp : g.IsPrime := Ideal.IsPrime.under _ _
  have hQ'0 : Q' ≠ ⊥ := by rintro rfl; exact hQ'e (Ideal.ramificationIdx_bot_eq_one _)
  have hg0 : g ≠ ⊥ := Ideal.IsIntegral.under_ne_bot ℚ[X] hQ'0
  have hXg : X ∉ g := fun hX => hne (eq_span_X_of_mem g hX)
  set h := g.comap σ with hh_def
  haveI hhp : h.IsPrime := Ideal.IsPrime.comap σ
  have hh0 : h ≠ ⊥ := by
    letI : Algebra SrcPoly ℚ[X] := (σ : SrcPoly →+* ℚ[X]).toAlgebra
    haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
    exact Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  have hXb : ∀ g' : Ideal ℚ[X], g'.IsPrime → g'.comap σ = h → X ∉ g' → X - C b ∉ h := by
    intro g' hg'p hg' hXg' hm
    rw [← hg'] at hm
    have hm' : σ (X - C b) ∈ g' := hm
    rw [map_sub, hσX, hσC, add_sub_cancel_left] at hm'
    rcases hg'p.mem_or_mem hm' with h1 | h1
    · exact hg'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h1
        (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hc))))
    · exact hXg' (hg'p.mem_of_pow_mem n h1)
  have hhS : ∀ b' ∈ S, h ≠ Ideal.span {X - C b'} := by
    intro b' hb' heq
    have hmem : X - C b' ∈ h := heq ▸ Ideal.mem_span_singleton_self _
    by_cases hbb : b' = b
    · subst hbb; exact hXb g hgp rfl hXg hmem
    · apply hS' b' hb' hbb
      have hm' : σ (X - C b') ∈ g := hmem
      have e : (X ^ n - C (c * (b' - b)) : ℚ[X]) = C c * σ (X - C b') := by
        rw [map_sub, hσX, hσC]
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        rw [C_mul, C_sub]
        linear_combination (-(X ^ n)) * h1
      rw [e]; exact Ideal.mul_mem_left _ _ hm'
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap ℚ[X] E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨X, rfl⟩
  refine compositum_core0 hU ℚ[X] (RatFunc ℚ) E E' ℚ[X] ι σ
    (finSubst_compat ι b c n hc hshape) (finite_of_isIntegral _ hint) hσinj (polyMap_injective E')
    h hh0 hadj ?_ ?_ Q' rfl
  · intro Q hQ hQu
    exact hE Q hQ (fun b' hb' => by rw [hQu]; exact hhS b' hb')
  · intro g' hg'p hg'
    have hg'0 : g' ≠ ⊥ := by
      rintro rfl
      apply hh0
      rw [← hg', Ideal.comap_bot_of_injective σ hσinj]
    have hXg' : X ∉ g' := by
      intro hX
      apply hhS b hbS
      have hm : X - C b ∈ h := by
        rw [← hg']
        change σ (X - C b) ∈ g'
        rw [map_sub, hσX, hσC, add_sub_cancel_left]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hX n hn)
      exact eq_span_of_irreducible_mem (irreducible_X_sub_C b) h hm
    exact polyUnram _ hrdeg hint g' hg'0 (derivative_notMem b c n hn hc g' hXg')

theorem sepCongr {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) [Algebra.HasSeparableResidueFieldsAt A B p] :
    Algebra.HasSeparableResidueFieldsAt A B q := by
  subst h
  assumption

/-- A finite separable extension, unramified at every prime over the maximal ideal of a DVR, has
formally unramified integral closure. -/
theorem fu_of_unram (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q)) :
    Algebra.FormallyUnramified R (integralClosure R L) := by
  classical
  set B := integralClosure R L
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Algebra.EssFiniteType R B := inferInstance
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  rw [Algebra.formallyUnramified_iff_forall]
  rintro ⟨q, hq⟩
  by_cases hq0 : q = ⊥
  · subst hq0
    change Algebra.FormallyUnramified R (Localization.AtPrime (⊥ : Ideal B))
    haveI : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
      simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
    let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] L :=
      IsLocalization.algEquiv (nonZeroDivisors B) _ L
    haveI : Algebra.FormallyUnramified R K := Algebra.FormallyUnramified.of_isLocalization
      (M := nonZeroDivisors R)
    haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
    haveI : Algebra.FormallyUnramified R L := Algebra.FormallyUnramified.comp R K L
    exact Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars R)
  · have hu0 : q.under R ≠ ⊥ := Ideal.IsIntegral.under_ne_bot R hq0
    haveI : (q.under R).IsPrime := Ideal.IsPrime.under R q
    have hu : q.under R = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hu0)
    haveI : q.LiesOver (maximalIdeal R) := ⟨hu.symm⟩
    have he := (h q).1
    haveI : Algebra.HasSeparableResidueFieldsAt R B (maximalIdeal R) := by
      constructor
      intro q' _ _
      letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) q'
      haveI : q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q'
        (by rw [← Ideal.LiesOver.over (P := q') (p := maximalIdeal R)]; infer_instance)
      haveI := (h q').2
      exact Algebra.isSeparable_residueField_iff.mpr inferInstance
    haveI : Algebra.HasSeparableResidueFieldsAt R B (q.under R) := sepCongr hu.symm
    exact (Ideal.ramificationIdx_eq_one_iff).mp he

/-- **`UnramCompositum` is proved.** Proof: the integral closures `B`, `B'` of `R` in `L`, `L'` are
formally unramified over `R` (`fu_of_unram`); the image `D` of `B ⊗_R B'` in `M` is finite and
formally unramified over `R`, so each localization of `D` at a maximal ideal has maximal ideal
generated by a uniformizer of `R`, hence is a DVR; so `D` is integrally closed, with fraction field
`M = L·L'`, hence `D` is the integral closure of `R` in `M`, which is therefore unramified. -/
theorem unramCompositum : UnramCompositum := by
  intro R K L L' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hadj hL hL' Q _ _
  classical
  set B := integralClosure R L
  set B' := integralClosure R L'
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply R K L])
  haveI : IsScalarTower R L' M := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply K L' M,
      ← IsScalarTower.algebraMap_apply R K L'])
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Module.Finite R B' := IsIntegralClosure.finite R K L' B'
  haveI hfB : Algebra.FormallyUnramified R B := fu_of_unram R K L hL
  haveI hfB' : Algebra.FormallyUnramified R B' := fu_of_unram R K L' hL'
  let fB : B →ₐ[R] M := (IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val
  let fB' : B' →ₐ[R] M := (IsScalarTower.toAlgHom R L' M).comp (integralClosure R L').val
  let φ : B ⊗[R] B' →ₐ[R] M :=
    Algebra.TensorProduct.lift fB fB' (fun _ _ => Commute.all _ _)
  set D : Subalgebra R M := φ.range
  haveI : Algebra.FormallyUnramified B (B ⊗[R] B') := inferInstance
  haveI : Algebra.FormallyUnramified R (B ⊗[R] B') := Algebra.FormallyUnramified.comp R B _
  haveI hfD : Algebra.FormallyUnramified R D :=
    Algebra.FormallyUnramified.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI hDfin : Module.Finite R D :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R K M]; exact (algebraMap K M).injective.comp hRK
  have hDinj : Function.Injective (algebraMap D M) := Subtype.val_injective
  have hRD : Function.Injective (algebraMap R D) := by
    intro x y hxy
    apply hRM
    have := congrArg Subtype.val hxy
    simpa using this
  have hfBD : ∀ b : B, fB b ∈ D := fun b => ⟨b ⊗ₜ 1, by simp [φ]⟩
  have hfB'D : ∀ b : B', fB' b ∈ D := fun b => ⟨1 ⊗ₜ b, by simp [φ]⟩
  -- the fraction field of `D` is `M`
  let F : Subfield M := (IsFractionRing.lift (K := FractionRing D) hDinj).fieldRange
  have hDF : ∀ d : D, (d : M) ∈ F := fun d =>
    ⟨algebraMap D (FractionRing D) d, IsFractionRing.lift_algebraMap _ _⟩
  have hF : ∀ (L₀ : Type) [Field L₀] [Algebra K L₀] [Algebra R L₀] [IsScalarTower R K L₀]
      [FiniteDimensional K L₀] [Algebra L₀ M] [IsScalarTower K L₀ M] (f₀ : integralClosure R L₀ →ₐ[R] M),
      (∀ b, f₀ b = algebraMap L₀ M b) → (∀ b, f₀ b ∈ D) → ∀ l : L₀, algebraMap L₀ M l ∈ F := by
    intro L₀ _ _ _ _ _ _ _ f₀ hf₀ hf₀D l
    have halg : IsAlgebraic R l :=
      (IsFractionRing.isAlgebraic_iff R K L₀).mpr (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    let b : integralClosure R L₀ := ⟨y • l, hyint⟩
    have hy : algebraMap R M y ≠ 0 := (map_ne_zero_iff _ hRM).mpr hy0
    have e : algebraMap L₀ M l = f₀ b / algebraMap R M y := by
      rw [eq_div_iff hy, hf₀]
      change _ = algebraMap L₀ M (y • l)
      rw [Algebra.smul_def, map_mul, mul_comm, IsScalarTower.algebraMap_apply R K L₀,
        IsScalarTower.algebraMap_apply R K M, ← IsScalarTower.algebraMap_apply K L₀ M]
    rw [e]
    refine div_mem (hDF ⟨_, hf₀D b⟩) ?_
    exact hDF (algebraMap R D y)
  have hLF := hF L fB (fun _ => rfl) hfBD
  have hL'F := hF L' fB' (fun _ => rfl) hfB'D
  have hFtop : F = ⊤ := by
    letI := (algebraMap L M)
    have h1 := congrArg IntermediateField.toSubfield hadj
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h1
    rw [eq_top_iff, ← h1, Subfield.closure_le]
    rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
    · exact hLF l
    · exact hL'F l
  haveI hFrac : IsFractionRing D M := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro z
      have hz : z ∈ F := hFtop ▸ Subfield.mem_top z
      obtain ⟨w, rfl⟩ := hz
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := D) w
      refine ⟨⟨x, ⟨y, hy⟩⟩, ?_⟩
      simp only [map_div₀, IsFractionRing.lift_algebraMap]
      exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro x y hxy
      exact ⟨1, by simp [hDinj hxy]⟩
  -- `D` is integrally closed
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing R D
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmaxR : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI hDic : IsIntegrallyClosed D := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P hP0 hPmax
    have hPu : P.under R = maximalIdeal R := IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R P)
    set Dp := Localization.AtPrime P
    haveI : IsLocalHom (algebraMap R Dp) := by
      constructor
      intro r hr
      by_contra hnu
      have hrm : r ∈ maximalIdeal R := hnu
      rw [← hPu] at hrm
      have : algebraMap D Dp (algebraMap R D r) ∈ maximalIdeal Dp := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hrm
      rw [← IsScalarTower.algebraMap_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hr
    haveI : Algebra.FormallyUnramified D Dp :=
      Algebra.FormallyUnramified.of_isLocalization (M := P.primeCompl)
    haveI : Algebra.FormallyUnramified R Dp := Algebra.FormallyUnramified.comp R D Dp
    haveI : Algebra.EssFiniteType D Dp := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType R Dp := Algebra.EssFiniteType.comp R D Dp
    have hmaxDp : maximalIdeal Dp = Ideal.span {algebraMap R Dp ϖ} := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := Dp), hmaxR, Ideal.map_span,
        Set.image_singleton]
    have hRDp : Function.Injective (algebraMap R Dp) := by
      rw [IsScalarTower.algebraMap_eq R D Dp]
      exact (IsLocalization.injective Dp P.primeCompl_le_nonZeroDivisors).comp hRD
    have hnf : ¬ IsField Dp := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmaxDp, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ hRDp] at this
      exact hϖ.ne_zero this
    have hprin : (maximalIdeal Dp).IsPrincipal := ⟨⟨_, hmaxDp⟩⟩
    haveI : IsDiscreteValuationRing Dp :=
      ((IsDiscreteValuationRing.TFAE Dp hnf).out 1 5).mpr hprin
    infer_instance
  -- `D` is the integral closure of `R` in `M`
  have hDC : D = integralClosure R M := by
    apply le_antisymm
    · intro x hx
      exact (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : D)).map (IsScalarTower.toAlgHom R D M)
    · intro x hx
      have hxD : IsIntegral D x := IsIntegral.tower_top hx
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := D) (K := M)).mp hxD
      exact y.2
  -- conclusion
  let eDC : D ≃ₐ[R] integralClosure R M := Subalgebra.equivOfEq D _ hDC
  haveI : Algebra.FormallyUnramified R (integralClosure R M) :=
    Algebra.FormallyUnramified.of_equiv eDC
  haveI : Module.Finite R (integralClosure R M) := Module.Finite.equiv eDC.toLinearEquiv
  haveI : Algebra.IsUnramifiedAt R Q :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨Q, inferInstance⟩
  refine ⟨Ideal.ramificationIdx_eq_one Q R, ?_⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal R)]; infer_instance)
  letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) Q
  have hsep := ((Algebra.isUnramifiedAt_iff_map_eq R (maximalIdeal R) Q).mp inferInstance).1
  exact Algebra.isSeparable_residueField_iff.mp hsep

/-- `ℚ → ℚ[1/X]`, constants. -/
def Cinf : ℚ →+* InfCoord := (Polynomial.C : ℚ →+* ℚ[X])

/-- The identity `ℚ[X] → InfCoord` (as types). -/
def toInf (f : ℚ[X]) : InfCoord := f

/-- **Transfer between `ℚ[1/X]` and `ℚ[X]` away from `0` and `∞`.** A prime `Q` of the integral
closure of `ℚ[1/X]` in `E` over a prime `h` with `1/X ∉ h` has the ramification index of a prime
`QX` of the integral closure of `ℚ[X]` in `E`; if `QX` lies over `X − b'`, then `b' ≠ 0` and
`b'·(1/X) − 1 ∈ h`. -/
theorem infTransfer (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] (h : Ideal InfCoord) [hh : h.IsPrime]
    (hu : infUnif ∉ h) :
    letI := infAlg E
    ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime → Q.under InfCoord = h →
      ∃ QX : Ideal (integralClosure ℚ[X] E), QX.IsPrime ∧
        QX.ramificationIdx ℚ[X] = Q.ramificationIdx InfCoord ∧
        ∀ b' : ℚ, QX.under ℚ[X] = Ideal.span {X - C b'} →
          b' ≠ 0 ∧ toInf (C b' * X - 1) ∈ h := by
  letI := infAlg E
  intro Q hQp hQu
  classical
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  set Rp := Localization.AtPrime h
  letI : Algebra Rp (RatFunc ℚ) := IsLocalization.localizationAlgebraOfSubmonoidLe Rp (RatFunc ℚ)
    h.primeCompl (nonZeroDivisors InfCoord) h.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower InfCoord Rp (RatFunc ℚ) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp (RatFunc ℚ)
      h.primeCompl (nonZeroDivisors InfCoord) h.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization h.primeCompl Rp (RatFunc ℚ)
  letI : Algebra Rp E := ((algebraMap (RatFunc ℚ) E).comp (algebraMap Rp (RatFunc ℚ))).toAlgebra
  haveI : IsScalarTower Rp (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower InfCoord Rp E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc ℚ) E (algebraMap InfCoord (RatFunc ℚ) x) =
      algebraMap (RatFunc ℚ) E (algebraMap Rp (RatFunc ℚ) (algebraMap InfCoord Rp x))
    rw [← IsScalarTower.algebraMap_apply InfCoord Rp (RatFunc ℚ)]
  have hRpK : Function.Injective (algebraMap Rp (RatFunc ℚ)) := IsFractionRing.injective Rp _
  -- the unit `μ` (image of `1/X`) and the map `τ : ℚ[X] → Rp`, `X ↦ μ⁻¹`
  have hμ : IsUnit (algebraMap InfCoord Rp infUnif) :=
    IsLocalization.map_units Rp (⟨infUnif, hu⟩ : h.primeCompl)
  set μ := hμ.unit with hμ_def
  let i0 : ℚ →+* Rp := (algebraMap InfCoord Rp).comp Cinf
  let τ : ℚ[X] →+* Rp := Polynomial.eval₂RingHom i0 (↑μ⁻¹ : Rp)
  have hevalμ : ∀ f : ℚ[X], eval₂ i0 (μ : Rp) f = algebraMap InfCoord Rp (toInf f) := by
    intro f
    have := Polynomial.hom_eval₂ f (Polynomial.C : ℚ →+* ℚ[X])
      (algebraMap InfCoord Rp : ℚ[X] →+* Rp) X
    rw [eval₂_C_X] at this
    rw [hμ_def, IsUnit.unit_spec]
    exact this.symm
  have hrefl : ∀ (f : ℚ[X]) (N : ℕ), f.natDegree ≤ N →
      τ (reflect N f) * (μ : Rp) ^ N = algebraMap InfCoord Rp (toInf f) := by
    intro f N hf
    letI : Invertible (μ : Rp) := μ.invertible
    have := eval₂_reflect_mul_pow i0 (μ : Rp) N f hf
    rw [hevalμ] at this
    rw [← this]
    rfl
  -- compatibility of `τ` with the maps to `ℚ(X)`
  have hτK : ∀ f : ℚ[X], algebraMap Rp (RatFunc ℚ) (τ f) = algebraMap ℚ[X] (RatFunc ℚ) f := by
    have : (algebraMap Rp (RatFunc ℚ)).comp τ = algebraMap ℚ[X] (RatFunc ℚ) := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap Rp (RatFunc ℚ)).comp τ).comp C)
          ((algebraMap ℚ[X] (RatFunc ℚ)).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        change algebraMap Rp (RatFunc ℚ) (eval₂ i0 (↑μ⁻¹ : Rp) X) = _
        rw [eval₂_X, RatFunc.algebraMap_X]
        have h1 : algebraMap Rp (RatFunc ℚ) (μ : Rp) = RatFunc.X⁻¹ := by
          rw [hμ_def, IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply]
          change eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (X : ℚ[X]) = _
          rw [eval₂_X]
        have h2 : algebraMap Rp (RatFunc ℚ) (↑μ⁻¹ : Rp) * algebraMap Rp (RatFunc ℚ) (μ : Rp) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [h1] at h2
        exact (mul_inv_eq_one₀ RatFunc.X_ne_zero).mp h2
    intro f
    exact congrArg (fun g => g f) this
  have hτinj : Function.Injective τ := by
    intro x y hxy
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    rw [← hτK, ← hτK, hxy]
  letI : Algebra ℚ[X] Rp := τ.toAlgebra
  haveI : IsScalarTower ℚ[X] Rp E := by
    apply IsScalarTower.of_algebraMap_eq
    intro f
    change algebraMap ℚ[X] E f = algebraMap (RatFunc ℚ) E (algebraMap Rp (RatFunc ℚ) (τ f))
    rw [hτK, ← IsScalarTower.algebraMap_apply]
  set hX : Ideal ℚ[X] := (maximalIdeal Rp).comap (algebraMap ℚ[X] Rp) with hX_def
  haveI : hX.IsPrime := Ideal.IsPrime.comap _
  -- `Rp` is the localization of `ℚ[X]` at `hX`
  haveI hlocX : IsLocalization.AtPrime Rp hX := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact (IsLocalRing.notMem_maximalIdeal).mp hy
    · intro z
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective h.primeCompl z
      set N := max (a : ℚ[X]).natDegree (s.1 : ℚ[X]).natDegree
      have ha := hrefl a N (le_max_left _ _)
      have hs := hrefl s.1 N (le_max_right _ _)
      have hsu : IsUnit (algebraMap InfCoord Rp s.1) := IsLocalization.map_units Rp s
      have hys : IsUnit (τ (reflect N (s.1 : ℚ[X]))) := by
        have : IsUnit (τ (reflect N (s.1 : ℚ[X])) * (μ : Rp) ^ N) := by rw [hs]; exact hsu
        exact isUnit_of_mul_isUnit_left this
      refine ⟨⟨reflect N (a : ℚ[X]), ⟨reflect N (s.1 : ℚ[X]), fun hm => ?_⟩⟩, ?_⟩
      · exact (IsLocalRing.notMem_maximalIdeal.mpr hys) hm
      · change IsLocalization.mk' Rp a s * τ (reflect N (s.1 : ℚ[X])) = τ (reflect N (a : ℚ[X]))
        have hμN : IsUnit ((μ : Rp) ^ N) := (Units.isUnit μ).pow N
        apply hμN.mul_right_cancel
        rw [mul_assoc, hs, ha]
        exact IsLocalization.mk'_spec Rp a s
    · intro x y hxy
      exact ⟨1, by simp [hτinj hxy]⟩
  -- integral closures
  have hP1 : ∀ x ∈ h.primeCompl, algebraMap InfCoord E x ≠ 0 := by
    intro x hx h0
    apply hx
    have hinj : Function.Injective (algebraMap InfCoord E) := by
      rw [IsScalarTower.algebraMap_eq InfCoord (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective _ _)
    rw [hinj (h0.trans (map_zero _).symm)]; exact h.zero_mem
  have hP2 : ∀ x ∈ hX.primeCompl, algebraMap ℚ[X] E x ≠ 0 := by
    intro x hx h0
    apply hx
    have hinj : Function.Injective (algebraMap ℚ[X] E) := by
      rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective _ _)
    rw [hinj (h0.trans (map_zero _).symm)]; exact hX.zero_mem
  obtain ⟨h11, h12, h13⟩ := intCl_isLocalization InfCoord Rp E h.primeCompl hP1
  obtain ⟨h21, h22, h23⟩ := intCl_isLocalization ℚ[X] Rp E hX.primeCompl hP2
  letI := (intClIncl InfCoord Rp E).toAlgebra
  letI := (intClIncl ℚ[X] Rp E).toAlgebra
  haveI : Q.LiesOver h := ⟨hQu.symm⟩
  set Qp := Q.map (algebraMap (integralClosure InfCoord E) (integralClosure Rp E))
  haveI : Qp.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver _ h _ Q
  haveI : Qp.LiesOver (maximalIdeal Rp) := IsLocalization.AtPrime.liesOver_map_of_liesOver h Rp _ Q
  have he1 : Qp.ramificationIdx Rp = Q.ramificationIdx InfCoord :=
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx h Rp _ Q
  set QX := Qp.comap (algebraMap (integralClosure ℚ[X] E) (integralClosure Rp E))
  haveI : QX.LiesOver hX := IsLocalization.AtPrime.liesOver_comap_of_liesOver hX Rp Qp
  haveI : QX.IsPrime := Ideal.IsPrime.comap _
  have hQpX : Qp = QX.map (algebraMap (integralClosure ℚ[X] E) (integralClosure Rp E)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure ℚ[X] E)
      hX.primeCompl) (integralClosure Rp E) Qp).symm
  have he2 : Qp.ramificationIdx Rp = QX.ramificationIdx ℚ[X] := by
    rw [hQpX]
    exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx hX Rp _ QX
  refine ⟨QX, inferInstance, he2.symm.trans he1, ?_⟩
  intro b' hb'
  have hmem : X - C b' ∈ hX := by
    have e0 : hX = QX.under ℚ[X] := Ideal.LiesOver.over
    rw [e0, hb']
    exact Ideal.mem_span_singleton_self _
  have hm : τ (X - C b') ∈ maximalIdeal Rp := hmem
  rw [map_sub] at hm
  change eval₂ i0 (↑μ⁻¹ : Rp) X - eval₂ i0 (↑μ⁻¹ : Rp) (C b') ∈ maximalIdeal Rp at hm
  rw [eval₂_X, eval₂_C] at hm
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [map_zero, sub_zero] at hm
    exact (IsLocalRing.notMem_maximalIdeal.mpr (Units.isUnit μ⁻¹)) hm
  · have hm2 : (μ : Rp) * (↑μ⁻¹ - i0 b') ∈ maximalIdeal Rp := Ideal.mul_mem_left _ _ hm
    have e : (μ : Rp) * (↑μ⁻¹ - i0 b') = -algebraMap InfCoord Rp (toInf (C b' * X - 1)) := by
      rw [mul_sub, Units.mul_inv, ← hevalμ]
      simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_one]
      ring
    rw [e, neg_mem_iff] at hm2
    rw [← Localization.AtPrime.comap_maximalIdeal (I := h)]
    exact hm2

/-- Compatibility of the Kummer substitution at `∞` (`1/X ↦ s^n/c`) with `ι`. -/
theorem infSubst_compat {E E' : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] (ι : E →+* E') (c : ℚ) (n : ℕ) (hc : c ≠ 0)
    (hshape : KummerShape E E' ι (rInf c n)) :
    letI := infAlg E
    ∀ x : InfCoord, algebraMap ℚ[X] E'
      ((Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n) : ℚ[X] →+* ℚ[X]) x) =
        ι (algebraMap InfCoord E x) := by
  letI := infAlg E
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
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

/-- **`KummerOtherBranchInf` from `UnramCompositum`.** -/
theorem kummerOtherBranchInf_of_unram (hU : UnramCompositum) : KummerOtherBranchInf := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι c n hn hc hshape S hE Q' hQ'p hQ'e
  classical
  letI := infAlg E
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  letI : IsDedekindDomain InfCoord := inferInstanceAs (IsDedekindDomain ℚ[X])
  letI : Algebra ℚ InfCoord := inferInstanceAs (Algebra ℚ ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  let σ : InfCoord →+* ℚ[X] := σ0
  have hσC : ∀ a : ℚ, σ0 (C a) = C a := fun a => by simp [σ0]
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
  have hsn : σ0 (C c * X) = X ^ n := by
    rw [map_mul, hσC, hσX, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ0.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * X), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hint : σ0.IsIntegral := isIntegral_of_X σ0 hσC hXint
  have hrdeg : 0 < (C c⁻¹ * X ^ n : ℚ[X]).natDegree := by
    rw [natDegree_C_mul_X_pow n _ (inv_ne_zero hc)]; exact hn
  have hσinj : Function.Injective σ0 := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.comp (C c⁻¹ * X ^ n) = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso
      have := congrArg natDegree hr'
      rw [natDegree_C] at this; omega
  have hσu : ∀ g' : Ideal ℚ[X], g'.IsPrime → X ∉ g' → σ infUnif ∉ g' := by
    intro g' hg'p hXg' hm
    change σ0 X ∈ g' at hm
    rw [hσX] at hm
    rcases hg'p.mem_or_mem hm with h1 | h1
    · exact hg'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h1
        (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hc))))
    · exact hXg' (hg'p.mem_of_pow_mem n h1)
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hS'⟩ := hcon
  apply hQ'e
  set g := Q'.under ℚ[X] with hg_def
  haveI hgp : g.IsPrime := Ideal.IsPrime.under _ _
  have hQ'0 : Q' ≠ ⊥ := by rintro rfl; exact hQ'e (Ideal.ramificationIdx_bot_eq_one _)
  have hg0 : g ≠ ⊥ := Ideal.IsIntegral.under_ne_bot ℚ[X] hQ'0
  have hXg : X ∉ g := fun hX => hne (eq_span_X_of_mem g hX)
  set h := g.comap σ with hh_def
  haveI hhp : h.IsPrime := Ideal.IsPrime.comap σ
  have hh0 : h ≠ ⊥ := by
    letI : Algebra SrcPoly ℚ[X] := (σ0 : SrcPoly →+* ℚ[X]).toAlgebra
    haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
    exact Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  have hu : infUnif ∉ h := hσu g hgp hXg
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap ℚ[X] E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨X, rfl⟩
  refine compositum_core0 hU InfCoord (RatFunc ℚ) E E' ℚ[X] ι σ
    (infSubst_compat ι c n hc hshape) (finite_of_isIntegral _ hint) hσinj (polyMap_injective E')
    h hh0 hadj ?_ ?_ Q' rfl
  · intro Q hQ hQu
    obtain ⟨QX, hQXp, heq, hb⟩ := infTransfer E h hu Q hQ hQu
    rw [← heq]
    apply hE QX hQXp
    intro b' hb' hQXb
    obtain ⟨hb'0, hmem⟩ := hb b' hQXb
    apply hS' b' hb' hb'0
    have hm : σ (toInf (C b' * X - 1)) ∈ g := hmem
    have e : (C b' * X ^ n - C c : ℚ[X]) = C c * σ (toInf (C b' * X - 1)) := by
      change _ = C c * σ0 (C b' * X - 1)
      rw [map_sub, map_mul, hσC, hσX, map_one]
      have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
      linear_combination (-(C b' * X ^ n)) * h1
    rw [e]; exact Ideal.mul_mem_left _ _ hm
  · intro g' hg'p hg'
    have hg'0 : g' ≠ ⊥ := by
      rintro rfl
      apply hh0
      rw [← hg']
      exact Ideal.comap_bot_of_injective σ hσinj
    have hXg' : X ∉ g' := by
      intro hX
      apply hu
      rw [← hg']
      have : σ0 X ∈ g' := by
        rw [hσX]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hX n hn)
      exact this
    have hder := derivative_notMem 0 c n hn hc g' hXg'
    rw [C_0, zero_add] at hder
    exact polyUnram _ hrdeg hint g' hg'0 hder

/-- **Unramified base change (DVR form), proved.** `R`, `T` discrete valuation rings with fraction
fields `K`, `K'`; `σ : R → T` any ring map; `L/K` finite separable; `M` a field generated by `ι(L)`
and `K'`, compatibly with `σ` on `R`. If the integral closure of `R` in `L` is unramified over the
maximal ideal of `R` (with separable residue fields), then every prime of the integral closure of
`T` in `M` over the maximal ideal of `T` has ramification index `1`. (Same proof as
`unramCompositum`, with `T ⊗_R B` in place of `B ⊗_R B'`.) -/
theorem unramBaseChange (R K L M T K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K'] [Algebra T K'] [IsFractionRing T K'] [Algebra K' M] [Algebra T M]
    [IsScalarTower T K' M]
    (ι : L →+* M) (σ : R →+* T) (hσ : ∀ x, algebraMap T M (σ x) = ι (algebraMap R L x))
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L (Set.range (algebraMap K' M)) = ⊤)
    (hL : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q))
    (Q : Ideal (integralClosure T M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal T)] :
    Q.ramificationIdx T = 1 ∧
      Algebra.IsSeparable (T ⧸ maximalIdeal T) (integralClosure T M ⧸ Q) := by
  classical
  letI : Algebra R T := σ.toAlgebra
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra R M := ((algebraMap T M).comp σ).toAlgebra
  haveI : IsScalarTower R T M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq (fun x => hσ x)
  set B := integralClosure R L
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI hfB : Algebra.FormallyUnramified R B := fu_of_unram R K L hL
  let fB : B →ₐ[R] M := (IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val
  let φ : T ⊗[R] B →ₐ[T] M :=
    Algebra.TensorProduct.lift (Algebra.ofId T M) fB (fun _ _ => Commute.all _ _)
  set D : Subalgebra T M := φ.range
  haveI : Algebra.FormallyUnramified T (T ⊗[R] B) := inferInstance
  haveI hfD : Algebra.FormallyUnramified T D :=
    Algebra.FormallyUnramified.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Module.Finite T (T ⊗[R] B) := inferInstance
  haveI hDfin : Module.Finite T D :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hTK : Function.Injective (algebraMap T K') := IsFractionRing.injective T K'
  have hTM : Function.Injective (algebraMap T M) := by
    rw [IsScalarTower.algebraMap_eq T K' M]; exact (algebraMap K' M).injective.comp hTK
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R L M, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap L M).injective.comp ((algebraMap K L).injective.comp hRK)
  have hDinj : Function.Injective (algebraMap D M) := Subtype.val_injective
  have hTD : Function.Injective (algebraMap T D) := by
    intro x y hxy
    apply hTM
    have := congrArg Subtype.val hxy
    simpa using this
  have hfBD : ∀ b : B, fB b ∈ D := fun b => ⟨1 ⊗ₜ b, by simp [φ]⟩
  have hRD : ∀ r : R, algebraMap R M r ∈ D := fun r => by
    rw [IsScalarTower.algebraMap_apply R T M]; exact D.algebraMap_mem _
  -- the fraction field of `D` is `M`
  let F : Subfield M := (IsFractionRing.lift (K := FractionRing D) hDinj).fieldRange
  have hDF : ∀ x ∈ D, x ∈ F := fun x hx =>
    ⟨algebraMap D (FractionRing D) ⟨x, hx⟩, IsFractionRing.lift_algebraMap _ _⟩
  have hLF : ∀ l : L, algebraMap L M l ∈ F := by
    intro l
    have halg : IsAlgebraic R l :=
      (IsFractionRing.isAlgebraic_iff R K L).mpr (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    let b : B := ⟨y • l, hyint⟩
    have hy : algebraMap R M y ≠ 0 := (map_ne_zero_iff _ hRM).mpr hy0
    have e : algebraMap L M l = fB b / algebraMap R M y := by
      rw [eq_div_iff hy]
      change _ = algebraMap L M (y • l)
      rw [Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply R L M]
    rw [e]
    exact div_mem (hDF _ (hfBD b)) (hDF _ (hRD y))
  have hK'F : ∀ k : K', algebraMap K' M k ∈ F := by
    intro k
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := T) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (hDF _ (D.algebraMap_mem x)) (hDF _ (D.algebraMap_mem y))
  have hFtop : F = ⊤ := by
    have h1 := congrArg IntermediateField.toSubfield hadj
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h1
    rw [eq_top_iff, ← h1, Subfield.closure_le]
    rintro _ (⟨l, rfl⟩ | ⟨k, rfl⟩)
    · exact hLF l
    · exact hK'F k
  haveI hFrac : IsFractionRing D M := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro z
      have hz : z ∈ F := hFtop ▸ Subfield.mem_top z
      obtain ⟨w, rfl⟩ := hz
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := D) w
      refine ⟨⟨x, ⟨y, hy⟩⟩, ?_⟩
      simp only [map_div₀, IsFractionRing.lift_algebraMap]
      exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro x y hxy
      exact ⟨1, by simp [hDinj hxy]⟩
  -- `D` is integrally closed
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing T D
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmaxT : maximalIdeal T = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI hDic : IsIntegrallyClosed D := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P hP0 hPmax
    have hPu : P.under T = maximalIdeal T := IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under T P)
    set Dp := Localization.AtPrime P
    haveI : IsLocalHom (algebraMap T Dp) := by
      constructor
      intro r hr
      by_contra hnu
      have hrm : r ∈ maximalIdeal T := hnu
      rw [← hPu] at hrm
      have : algebraMap D Dp (algebraMap T D r) ∈ maximalIdeal Dp := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hrm
      rw [← IsScalarTower.algebraMap_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hr
    haveI : Algebra.FormallyUnramified D Dp :=
      Algebra.FormallyUnramified.of_isLocalization (M := P.primeCompl)
    haveI : Algebra.FormallyUnramified T Dp := Algebra.FormallyUnramified.comp T D Dp
    haveI : Algebra.EssFiniteType D Dp := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType T Dp := Algebra.EssFiniteType.comp T D Dp
    have hmaxDp : maximalIdeal Dp = Ideal.span {algebraMap T Dp ϖ} := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := T) (S := Dp), hmaxT, Ideal.map_span,
        Set.image_singleton]
    have hTDp : Function.Injective (algebraMap T Dp) := by
      rw [IsScalarTower.algebraMap_eq T D Dp]
      exact (IsLocalization.injective Dp P.primeCompl_le_nonZeroDivisors).comp hTD
    have hnf : ¬ IsField Dp := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmaxDp, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ hTDp] at this
      exact hϖ.ne_zero this
    have hprin : (maximalIdeal Dp).IsPrincipal := ⟨⟨_, hmaxDp⟩⟩
    haveI : IsDiscreteValuationRing Dp :=
      ((IsDiscreteValuationRing.TFAE Dp hnf).out 1 5).mpr hprin
    infer_instance
  -- `D` is the integral closure of `T` in `M`
  have hDC : D = integralClosure T M := by
    apply le_antisymm
    · intro x hx
      exact (Algebra.IsIntegral.isIntegral (R := T) (⟨x, hx⟩ : D)).map (IsScalarTower.toAlgHom T D M)
    · intro x hx
      have hxD : IsIntegral D x := IsIntegral.tower_top hx
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := D) (K := M)).mp hxD
      exact y.2
  let eDC : D ≃ₐ[T] integralClosure T M := Subalgebra.equivOfEq D _ hDC
  haveI : Algebra.FormallyUnramified T (integralClosure T M) :=
    Algebra.FormallyUnramified.of_equiv eDC
  haveI : Module.Finite T (integralClosure T M) := Module.Finite.equiv eDC.toLinearEquiv
  haveI : Algebra.IsUnramifiedAt T Q :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨Q, inferInstance⟩
  refine ⟨Ideal.ramificationIdx_eq_one Q T, ?_⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := T) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal T)]; infer_instance)
  letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal T) Q
  have hsep := ((Algebra.isUnramifiedAt_iff_map_eq T (maximalIdeal T) Q).mp inferInstance).1
  exact Algebra.isSeparable_residueField_iff.mp hsep

theorem mem_vertPrime_iff (p : ℕ) (f : ℤ[X]) :
    f ∈ vertPrime p ↔ f.map (Int.castRingHom (ZMod p)) = 0 := by
  rw [vertPrime, Ideal.mem_map_C_iff]
  constructor
  · intro h
    ext k
    rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Ideal.mem_span_singleton.mp (h k)
  · intro h k
    have := congrArg (fun g => g.coeff k) h
    simp only [coeff_map, coeff_zero, eq_intCast] at this
    exact Ideal.mem_span_singleton.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this)

theorem C_mem_vertPrime (p : ℕ) (m : ℤ) : C m ∈ vertPrime p ↔ (p : ℤ) ∣ m := by
  rw [mem_vertPrime_iff, Polynomial.map_C, C_eq_zero, eq_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem not_dvd_num_of_val_zero (p : ℕ) [hp : Fact p.Prime] (c : ℚ) (hc : c ≠ 0)
    (h : padicValRat p c = 0) : ¬ (p : ℤ) ∣ c.num := by
  intro hd
  have h1 : padicValNat p c.den = 0 :=
    padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p c (by rw [h]))
  have h2 : 1 ≤ padicValInt p c.num := by
    rcases (padicValInt_dvd_iff 1 c.num).mp (by simpa using hd) with h0 | h0
    · exact absurd h0 (Rat.num_ne_zero.mpr hc)
    · exact h0
  rw [padicValRat_def, h1] at h
  omega

/-- `ℤ[X]_(p)` is a discrete valuation ring. -/
theorem zxLoc_dvr (p : ℕ) (hp : p.Prime) :
    haveI := vertPrime_isPrime p hp
    IsDiscreteValuationRing (Localization.AtPrime (vertPrime p)) := by
  haveI := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  have hCp0 : algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ)) ≠ 0 := by
    intro h0
    have := IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
      (h0.trans (map_zero _).symm)
    rw [C_eq_zero] at this
    exact hp.ne_zero (by exact_mod_cast this)
  have h3 : 𝔭 = Ideal.span {C (p : ℤ)} := by
    rw [h𝔭, vertPrime, Ideal.map_span, Set.image_singleton]
  have hmax : maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ))} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine (congrArg (Ideal.map (algebraMap ℤ[X] (Localization.AtPrime 𝔭))) h3).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime 𝔭) := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    rw [hmax, Ideal.span_singleton_eq_bot] at this
    exact hCp0 this
  have hprin : (maximalIdeal (Localization.AtPrime 𝔭)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔭) hnf).out 1 5).mpr hprin

/-- A localization-compatible lift: `ℤ[X] → R` with every `f ∉ (p)` sent to a unit extends to
`ℤ[X]_(p)`; the image of a substitution is computed through `ℚ(X)`. Generic unit criterion:
if `g(β) · s^d = (image of F)` with `s` a unit and `F ∉ (p)`, then `g(β)` is a unit. -/
theorem unit_of_scaleRoots (p : ℕ) (hp : p.Prime) (N : ℤ[X]) (s : ℤ) (hs : ¬ (p : ℤ) ∣ s)
    (hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree) :
    haveI := vertPrime_isPrime p hp
    ∀ (β : Localization.AtPrime (vertPrime p)),
      (s : Localization.AtPrime (vertPrime p)) * β =
        algebraMap ℤ[X] (Localization.AtPrime (vertPrime p)) N →
      ∀ f : ℤ[X], f ∉ vertPrime p →
        IsUnit (Polynomial.eval₂ (Int.castRingHom _) β f) := by
  haveI := vertPrime_isPrime p hp
  haveI : Fact p.Prime := ⟨hp⟩
  set 𝔭 := vertPrime p
  set Rz := Localization.AtPrime 𝔭
  intro β hβ f hf
  have hsu : IsUnit (s : Rz) := by
    have : IsUnit (algebraMap ℤ[X] Rz (C s)) :=
      IsLocalization.map_units Rz (⟨C s, (C_mem_vertPrime p s).not.mpr hs⟩ : 𝔭.primeCompl)
    simpa using this
  have key := Polynomial.scaleRoots_eval₂_mul (p := f) (Int.castRingHom Rz) β s
  rw [eq_intCast, hβ] at key
  have hcomp : eval₂ (Int.castRingHom Rz) (algebraMap ℤ[X] Rz N) (scaleRoots f s) =
      algebraMap ℤ[X] Rz ((scaleRoots f s).comp N) := by
    rw [Polynomial.comp, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  rw [hcomp] at key
  set F := (scaleRoots f s).comp N
  have hF : F ∉ 𝔭 := by
    rw [mem_vertPrime_iff, Polynomial.map_comp]
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · obtain ⟨k, hk⟩ : ∃ k, ¬ (p : ℤ) ∣ f.coeff k := by
        by_contra hcon
        push_neg at hcon
        exact hf ((mem_vertPrime_iff p f).mpr (by
          ext k; rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hcon k))
      have := congrArg (fun g => g.coeff k) h0
      simp only [coeff_map, coeff_scaleRoots, coeff_zero, map_mul, map_pow, eq_intCast] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1)
      · exact hs ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (pow_eq_zero_iff'.mp h1).1)
    · have := congrArg natDegree h0
      rw [natDegree_C] at this
      omega
  have hFu : IsUnit (algebraMap ℤ[X] Rz F) := IsLocalization.map_units Rz (⟨F, hF⟩ : 𝔭.primeCompl)
  rw [key] at hFu
  exact isUnit_of_mul_isUnit_right hFu

/-- Common setup of the vertical pieces: `Rz = ℤ[X]_(p)` and its maps. -/
theorem locAlg_tower (p : ℕ) (hp : p.Prime) (F : Type) [Field F] [Algebra (RatFunc ℚ) F]
    [Algebra ℚ[X] F] [IsScalarTower ℚ[X] (RatFunc ℚ) F] :
    haveI := vertPrime_isPrime p hp
    letI : Algebra (Localization.AtPrime (vertPrime p)) (RatFunc ℚ) :=
      locAlg (RatFunc ℚ) (vertPrime p)
    letI : Algebra (Localization.AtPrime (vertPrime p)) F := locAlg F (vertPrime p)
    IsScalarTower (Localization.AtPrime (vertPrime p)) (RatFunc ℚ) F := by
  haveI := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p
  letI : Algebra (Localization.AtPrime 𝔭) (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI : Algebra (Localization.AtPrime 𝔭) F := locAlg F 𝔭
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext 𝔭.primeCompl
  rw [RingHom.comp_assoc]
  change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)) =
    (algebraMap (RatFunc ℚ) F).comp
      ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)))
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
  simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

/-- Localization transfer, downwards, for any localization `Rp` of `R0` at `p`. -/
theorem locTransfer_down' (R0 Rp F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [CommRing Rp] [Algebra R0 Rp] [IsLocalization.AtPrime Rp p]
    [IsLocalRing Rp] [Algebra Rp F] [IsScalarTower R0 Rp F]
    (hinj : Function.Injective (algebraMap R0 F))
    (Q : Ideal (integralClosure Rp F)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)] :
    letI := (intClIncl R0 Rp F).toAlgebra
    ∃ P0 : Ideal (integralClosure R0 F), P0.IsPrime ∧ P0.under R0 = p ∧
      Q.ramificationIdx Rp = P0.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 Rp F p.primeCompl hP
  letI := (intClIncl R0 Rp F).toAlgebra
  set P0 := Q.comap (algebraMap (integralClosure R0 F) (integralClosure Rp F))
  haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rp Q
  haveI : P0.IsPrime := Ideal.IsPrime.comap _
  have hQ : Q = P0.map (algebraMap (integralClosure R0 F) (integralClosure Rp F)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 F) p.primeCompl)
      (integralClosure Rp F) Q).symm
  refine ⟨P0, inferInstance, (Ideal.LiesOver.over (P := P0) (p := p)).symm, ?_⟩
  rw [hQ]
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp _ P0

/-- `E` with `[E : ℚ(X)] < p` and no vertical ramification at `p` is unramified, with separable
residue fields, over (any copy `Rz` of) `ℤ[X]_(p)`. -/
theorem vertical_hL (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (hdeg : Module.finrank (RatFunc ℚ) E < p) (hV : NoVerticalRam E p)
    (Rz : Type) [CommRing Rz] [IsDomain Rz] [IsDiscreteValuationRing Rz] [Algebra ℤ[X] Rz]
    [hloc : @IsLocalization.AtPrime ℤ[X] _ Rz _ _ (vertPrime p) (vertPrime_isPrime p hp)]
    [Algebra Rz (RatFunc ℚ)] [IsFractionRing Rz (RatFunc ℚ)] [Algebra Rz E]
    [IsScalarTower Rz (RatFunc ℚ) E]
    (htow : ∀ f : ℤ[X], algebraMap Rz E (algebraMap ℤ[X] Rz f) = zxMap E f) :
    ∀ (Q : Ideal (integralClosure Rz E)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rz)],
      Q.ramificationIdx Rz = 1 ∧
      Algebra.IsSeparable (Rz ⧸ maximalIdeal Rz) (integralClosure Rz E ⧸ Q) := by
  intro Q hQp hQl
  haveI := vertPrime_isPrime p hp
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra ℤ[X] E := intPolyAlg E
  haveI : IsScalarTower ℤ[X] Rz E := IsScalarTower.of_algebraMap_eq (fun f => (htow f).symm)
  obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down' ℤ[X] Rz E (vertPrime p) (zxMap_injective E) Q
  refine ⟨he.trans (hV P0 hP0 hP0u), ?_⟩
  haveI : IsFractionRing (integralClosure Rz E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc ℚ) E
  haveI : Module.Finite Rz (integralClosure Rz E) :=
    IsIntegralClosure.finite Rz (RatFunc ℚ) E (integralClosure Rz E)
  haveI hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rz) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rz)]; infer_instance)
  have hmax0 : maximalIdeal Rz ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  haveI : Algebra.IsSeparable (RatFunc ℚ) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsDedekindDomain (integralClosure Rz E) := integralClosure.isDedekindDomain Rz (RatFunc ℚ) E
  have hRzE : Function.Injective (algebraMap Rz (integralClosure Rz E)) := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    change algebraMap Rz E x = algebraMap Rz E y at h1
    rw [IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E] at h1
    exact IsFractionRing.injective Rz (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h1)
  haveI : NoZeroSMulDivisors Rz (integralClosure Rz E) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (hRzE (h1.trans (map_zero _).symm))
    · exact Or.inr h1⟩
  have hf := Ideal.inertiaDeg_le_finrank (integralClosure Rz E) (RatFunc ℚ) E Q hmax0
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  letI : Field (Rz ⧸ maximalIdeal Rz) := Ideal.Quotient.field _
  letI : Field (integralClosure Rz E ⧸ Q) := Ideal.Quotient.field _
  haveI : CharP (Rz ⧸ maximalIdeal Rz) p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hpm : algebraMap ℤ[X] Rz (C (p : ℤ)) ∈ maximalIdeal Rz := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (vertPrime p) Rz]
      exact Ideal.mem_map_of_mem _ ((C_mem_vertPrime p p).mpr dvd_rfl)
    have : ((p : ℕ) : Rz) = algebraMap ℤ[X] Rz (C (p : ℤ)) := by simp
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal Rz)), this, Ideal.Quotient.eq_zero_iff_mem]
    exact hpm
  exact isSeparable_of_finrank_lt p (lt_of_le_of_lt hf hdeg)

/-- **`KummerVerticalFin` is proved** (unramified base change along `ℤ[X]_(p) → ℤ[s]_(p)`,
`X ↦ b + s^n/c`). -/
theorem kummerVerticalFin_proof : KummerVerticalFin := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι b c n p hp hn hnp hdeg hc hcp hbp hshape hV
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI h𝔭p := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  set Rz := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Rz := zxLoc_dvr p hp
  letI iK : Algebra Rz (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI iE : Algebra Rz E := locAlg E 𝔭
  letI iE' : Algebra Rz E' := locAlg E' 𝔭
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  haveI : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  haveI : IsScalarTower ℤ[X] Rz (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  haveI : IsFractionRing Rz (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
  haveI : IsScalarTower Rz (RatFunc ℚ) E := locAlg_tower p hp E
  haveI : IsScalarTower Rz (RatFunc ℚ) E' := locAlg_tower p hp E'
  -- numerators and denominators of `b`, `c`
  have hbd : ¬ (p : ℤ) ∣ (b.den : ℤ) := by
    have := not_dvd_den_of_nonneg p b hbp
    exact_mod_cast this
  have hcd : ¬ (p : ℤ) ∣ (c.den : ℤ) := by
    have := not_dvd_den_of_nonneg p c (by rw [hcp])
    exact_mod_cast this
  have hcn : ¬ (p : ℤ) ∣ c.num := not_dvd_num_of_val_zero p c hc hcp
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨s, hs_def⟩ : ∃ s : ℤ, s = (b.den : ℤ) * c.num := ⟨_, rfl⟩
  have hs : ¬ (p : ℤ) ∣ s := fun h => (hpz.dvd_or_dvd (hs_def ▸ h)).elim hbd hcn
  obtain ⟨N, hN_def⟩ : ∃ N : ℤ[X], N = C (b.num * c.num) + C ((b.den : ℤ) * c.den) * X ^ n :=
    ⟨_, rfl⟩
  have hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree := by
    have h1 : (Int.castRingHom (ZMod p)) ((b.den : ℤ) * c.den) ≠ 0 := by
      rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact fun h => (hpz.dvd_or_dvd h).elim hbd hcd
    rw [hN_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, natDegree_C_add, natDegree_C_mul_X_pow n _ h1]
    exact hn
  have hCs : C s ∉ 𝔭 := (C_mem_vertPrime p s).not.mpr hs
  set β : Rz := IsLocalization.mk' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl) with hβ_def
  have hβ : (s : Rz) * β = algebraMap ℤ[X] Rz N := by
    have := IsLocalization.mk'_spec' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl)
    rw [← this]
    congr 1
    change (s : Rz) = algebraMap ℤ[X] Rz (C s)
    have e : (C s : ℤ[X]) = (s : ℤ[X]) := by simp
    rw [e, map_intCast]
  let σ0 : ℤ[X] →+* Rz := Polynomial.eval₂RingHom (Int.castRingHom Rz) β
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (σ0 y) := fun y =>
    unit_of_scaleRoots p hp N s hs hN β hβ y.1 y.2
  let σ : Rz →+* Rz := IsLocalization.lift (M := 𝔭.primeCompl) (S := Rz) (g := σ0) hunit
  have hσ0 : ∀ f : ℤ[X], σ (algebraMap ℤ[X] Rz f) = σ0 f := fun f => IsLocalization.lift_eq hunit f
  -- the image of `β` in `ℚ(X)` is `rFin b c n`
  have hs0 : (s : ℚ) ≠ 0 := by
    intro h0
    exact hs (by rw [show s = 0 by exact_mod_cast h0]; exact dvd_zero _)
  have e1 : (s : ℚ) * (b * c) = c * (b.num * c.num) := by
    have hb := Rat.mul_den_eq_num b
    rw [hs_def]; push_cast
    rw [← hb]; ring
  have e2 : (s : ℚ) = c * (b.den * c.den) := by
    have hc' := Rat.mul_den_eq_num c
    rw [hs_def]; push_cast
    rw [← hc']; ring
  have hpoly : C (s : ℚ) * (C (b * c) + X ^ n) = C c * N.map (Int.castRingHom ℚ) := by
    have hNm : N.map (Int.castRingHom ℚ) = C ((b.num * c.num : ℤ) : ℚ) +
        C (((b.den : ℤ) * c.den : ℤ) : ℚ) * X ^ n := by
      rw [hN_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, eq_intCast, eq_intCast]
    have e1' : (s : ℚ) * b * c = c * ((b.num * c.num : ℤ) : ℚ) := by
      rw [mul_assoc]; push_cast; exact e1
    have e2' : (s : ℚ) = c * (((b.den : ℤ) * c.den : ℤ) : ℚ) := by push_cast; exact e2
    rw [hNm]
    simp only [mul_add, ← mul_assoc, ← C_mul]
    rw [e1', ← e2']
  have hβK : algebraMap Rz (RatFunc ℚ) β = rFin b c n := by
    have h1 := congrArg (algebraMap Rz (RatFunc ℚ)) hβ
    rw [map_mul, map_intCast, ← IsScalarTower.algebraMap_apply] at h1
    have h2 := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hpoly
    simp only [map_mul] at h2
    have hsK : algebraMap ℚ[X] (RatFunc ℚ) (C (s : ℚ)) = (s : RatFunc ℚ) := by
      rw [RatFunc.algebraMap_C, map_intCast]
    have hCc : algebraMap ℚ[X] (RatFunc ℚ) (C c) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (C_ne_zero.mpr hc)
    have hsK0 : (s : RatFunc ℚ) ≠ 0 := by
      rw [← hsK]
      exact (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (C_ne_zero.mpr hs0)
    have h3 : algebraMap ℤ[X] (RatFunc ℚ) N = algebraMap ℚ[X] (RatFunc ℚ)
        (N.map (Int.castRingHom ℚ)) := rfl
    apply mul_left_cancel₀ hsK0
    rw [h1, h3, rFin, ← mul_div_assoc, eq_div_iff hCc, mul_comm _ (algebraMap ℚ[X] _ (C c)),
      ← h2, hsK, ← C_mul, add_comm]
  -- compatibility with `ι`
  have hσ : ∀ x, algebraMap Rz E' (σ x) = ι (algebraMap Rz E x) := by
    have : (algebraMap Rz E').comp σ = ι.comp (algebraMap Rz E) := by
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_int
          ((((algebraMap Rz E').comp σ).comp (algebraMap ℤ[X] Rz)).comp C)
          (((ι.comp (algebraMap Rz E)).comp (algebraMap ℤ[X] Rz)).comp C)) a
      · simp only [RingHom.comp_apply]
        rw [hσ0]
        change algebraMap Rz E' (eval₂ (Int.castRingHom Rz) β X) =
          ι (IsLocalization.lift _ (algebraMap ℤ[X] Rz X))
        rw [eval₂_X, IsLocalization.lift_eq, IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E', hβK]
        change _ = ι (algebraMap ℚ[X] E (X.map (Int.castRingHom ℚ)))
        rw [Polynomial.map_X, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          RatFunc.algebraMap_X, hshape.1]
    intro x
    exact RingHom.congr_fun this x
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap (RatFunc ℚ) E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨algebraMap ℚ[X] (RatFunc ℚ) X, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
  -- conclusion
  letI : Algebra ℤ[X] E' := intPolyAlg E'
  haveI : IsScalarTower ℤ[X] Rz E' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  intro Q' hQ'p hQ'u
  haveI : Q'.LiesOver 𝔭 := ⟨hQ'u.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up ℤ[X] E' 𝔭 (zxMap_injective E') Q'
  rw [← hQpe]
  exact (unramBaseChange Rz (RatFunc ℚ) E E' Rz (RatFunc ℚ) ι σ hσ hadj
    (vertical_hL E p hp hdeg hV Rz (fun f => IsLocalization.lift_eq _ f)) Qp).1
/-- **`KummerVerticalInf` is proved** (unramified base change along `ℤ[X]_(p) → ℤ[s]_(p)`,
`X ↦ c/s^n`). -/
theorem kummerVerticalInf_proof : KummerVerticalInf := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι c n p hp hn hnp hdeg hc hcp hshape hV
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI h𝔭p := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  set Rz := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Rz := zxLoc_dvr p hp
  letI iK : Algebra Rz (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI iE : Algebra Rz E := locAlg E 𝔭
  letI iE' : Algebra Rz E' := locAlg E' 𝔭
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  haveI : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  haveI : IsScalarTower ℤ[X] Rz (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  haveI : IsFractionRing Rz (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
  haveI : IsScalarTower Rz (RatFunc ℚ) E := locAlg_tower p hp E
  haveI : IsScalarTower Rz (RatFunc ℚ) E' := locAlg_tower p hp E'
  -- numerator and denominator of `c`
  have hcd : ¬ (p : ℤ) ∣ (c.den : ℤ) := by
    have := not_dvd_den_of_nonneg p c (by rw [hcp])
    exact_mod_cast this
  have hcn : ¬ (p : ℤ) ∣ c.num := not_dvd_num_of_val_zero p c hc hcp
  obtain ⟨s, hs_def⟩ : ∃ s : ℤ, s = c.num := ⟨_, rfl⟩
  have hs : ¬ (p : ℤ) ∣ s := hs_def ▸ hcn
  obtain ⟨N, hN_def⟩ : ∃ N : ℤ[X], N = C (c.den : ℤ) * X ^ n := ⟨_, rfl⟩
  have h1 : (Int.castRingHom (ZMod p)) (c.den : ℤ) ≠ 0 := by
    rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcd
  have hNmap : N.map (Int.castRingHom (ZMod p)) =
      C ((Int.castRingHom (ZMod p)) (c.den : ℤ)) * X ^ n := by
    rw [hN_def, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  have hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree := by
    rw [hNmap, natDegree_C_mul_X_pow n _ h1]
    exact hn
  have hN𝔭 : N ∉ 𝔭 := by
    rw [mem_vertPrime_iff, hNmap]
    exact mul_ne_zero (C_ne_zero.mpr h1) (pow_ne_zero _ X_ne_zero)
  have hCs : C s ∉ 𝔭 := (C_mem_vertPrime p s).not.mpr hs
  -- `β' = s^n/c` and `β = c/s^n`
  set β' : Rz := IsLocalization.mk' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl) with hβ'_def
  have hβ' : (s : Rz) * β' = algebraMap ℤ[X] Rz N := by
    have := IsLocalization.mk'_spec' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl)
    rw [← this]
    congr 1
    change (s : Rz) = algebraMap ℤ[X] Rz (C s)
    have e : (C s : ℤ[X]) = (s : ℤ[X]) := by simp
    rw [e, map_intCast]
  set β : Rz := IsLocalization.mk' Rz (C s) (⟨N, hN𝔭⟩ : 𝔭.primeCompl) with hβ_def
  have hββ' : β * β' = 1 :=
    IsLocalization.mk'_mul_mk'_eq_one (⟨C s, hCs⟩ : 𝔭.primeCompl) (⟨N, hN𝔭⟩ : 𝔭.primeCompl)
  letI : Invertible β := ⟨β', by rw [mul_comm]; exact hββ', hββ'⟩
  have hβu : IsUnit β := isUnit_of_invertible β
  let σ0 : ℤ[X] →+* Rz := Polynomial.eval₂RingHom (Int.castRingHom Rz) β
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (σ0 y) := by
    intro y
    set f := (y : ℤ[X])
    have hf : f ∉ 𝔭 := y.2
    set d := f.natDegree
    have hrefl : reflect d f ∉ 𝔭 := by
      intro hm
      apply hf
      change reflect d f ∈ Ideal.map C (Ideal.span {(p : ℤ)}) at hm
      change f ∈ Ideal.map C (Ideal.span {(p : ℤ)})
      rw [Ideal.mem_map_C_iff] at hm ⊢
      intro k
      by_cases hk : k ≤ d
      · have := hm (revAt d k)
        rwa [coeff_reflect, revAt_invol] at this
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        exact Ideal.zero_mem _
    have h1 := unit_of_scaleRoots p hp N s hs hN β' hβ' (reflect d f) hrefl
    have h2 := eval₂_reflect_mul_pow (Int.castRingHom Rz) β d f le_rfl
    change IsUnit (eval₂ (Int.castRingHom Rz) β f)
    rw [← h2]
    refine IsUnit.mul ?_ (hβu.pow d)
    convert h1
  let σ : Rz →+* Rz := IsLocalization.lift (M := 𝔭.primeCompl) (S := Rz) (g := σ0) hunit
  have hσ0 : ∀ f : ℤ[X], σ (algebraMap ℤ[X] Rz f) = σ0 f := fun f => IsLocalization.lift_eq hunit f
  -- the image of `β` in `ℚ(X)` is `rInf c n`
  have hβK : algebraMap Rz (RatFunc ℚ) β = rInf c n := by
    have hspec := IsLocalization.mk'_spec' Rz (C s) (⟨N, hN𝔭⟩ : 𝔭.primeCompl)
    have h1 := congrArg (algebraMap Rz (RatFunc ℚ)) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    change algebraMap ℤ[X] (RatFunc ℚ) N * algebraMap Rz (RatFunc ℚ) β =
      algebraMap ℤ[X] (RatFunc ℚ) (C s) at h1
    have hNK : algebraMap ℤ[X] (RatFunc ℚ) N = algebraMap ℚ[X] (RatFunc ℚ) (C (c.den : ℚ) * X ^ n) := by
      change algebraMap ℚ[X] (RatFunc ℚ) (N.map (Int.castRingHom ℚ)) = _
      rw [hN_def, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        eq_intCast, Int.cast_natCast]
    have hsK : algebraMap ℤ[X] (RatFunc ℚ) (C s) = algebraMap ℚ[X] (RatFunc ℚ) (C (c.num : ℚ)) := by
      change algebraMap ℚ[X] (RatFunc ℚ) ((C s).map (Int.castRingHom ℚ)) = _
      rw [Polynomial.map_C, eq_intCast, hs_def]
    have hN0 : algebraMap ℚ[X] (RatFunc ℚ) (C (c.den : ℚ) * X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast c.den_nz)) (pow_ne_zero _ X_ne_zero))
    have hXn : algebraMap ℚ[X] (RatFunc ℚ) (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (pow_ne_zero _ X_ne_zero)
    rw [hNK, hsK] at h1
    apply mul_left_cancel₀ hN0
    rw [h1, rInf, map_mul, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hXn, ← map_mul,
      ← C_mul, mul_comm ((c.den : ℚ)) c, Rat.mul_den_eq_num]
  -- compatibility with `ι`
  have hσ : ∀ x, algebraMap Rz E' (σ x) = ι (algebraMap Rz E x) := by
    have : (algebraMap Rz E').comp σ = ι.comp (algebraMap Rz E) := by
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_int
          ((((algebraMap Rz E').comp σ).comp (algebraMap ℤ[X] Rz)).comp C)
          (((ι.comp (algebraMap Rz E)).comp (algebraMap ℤ[X] Rz)).comp C)) a
      · simp only [RingHom.comp_apply]
        rw [hσ0]
        change algebraMap Rz E' (eval₂ (Int.castRingHom Rz) β X) =
          ι (IsLocalization.lift _ (algebraMap ℤ[X] Rz X))
        rw [eval₂_X, IsLocalization.lift_eq, IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E', hβK]
        change _ = ι (algebraMap ℚ[X] E (X.map (Int.castRingHom ℚ)))
        rw [Polynomial.map_X, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          RatFunc.algebraMap_X, hshape.1]
    intro x
    exact RingHom.congr_fun this x
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap (RatFunc ℚ) E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨algebraMap ℚ[X] (RatFunc ℚ) X, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
  -- conclusion
  letI : Algebra ℤ[X] E' := intPolyAlg E'
  haveI : IsScalarTower ℤ[X] Rz E' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  intro Q' hQ'p hQ'u
  haveI : Q'.LiesOver 𝔭 := ⟨hQ'u.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up ℤ[X] E' 𝔭 (zxMap_injective E') Q'
  rw [← hQpe]
  exact (unramBaseChange Rz (RatFunc ℚ) E E' Rz (RatFunc ℚ) ι σ hσ hadj
    (vertical_hL E p hp hdeg hV Rz (fun f => IsLocalization.lift_eq _ f)) Qp).1
/-- Every element of `ℚ(X)` lies in the subfield generated by `X`. -/
theorem ratFunc_mem_closure (z : RatFunc ℚ) : z ∈ Subfield.closure {(RatFunc.X : RatFunc ℚ)} := by
  have hpoly : ∀ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f ∈
      Subfield.closure {(RatFunc.X : RatFunc ℚ)} := by
    intro f
    induction f using Polynomial.induction_on with
    | C a =>
      rw [RatFunc.algebraMap_C, eq_ratCast]
      exact SubfieldClass.ratCast_mem _ a
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial k a _ =>
      rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
      exact mul_mem (by assumption) (Subfield.subset_closure rfl)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℚ[X]) z
  exact div_mem (hpoly a) (hpoly b)

/-- A non-constant rational function `P/Q` is transcendental over `ℚ`. -/
theorem ratFunc_transc (P Q : ℚ[X]) (hQ : Q ≠ 0) (hnc : ∀ a : ℚ, P ≠ C a * Q) (f : ℚ[X])
    (hf : aeval (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) f = 0) :
    f = 0 := by
  by_contra hf0
  set x := algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q
  have hxQ : IsIntegral ℚ x := (isAlgebraic_iff_isIntegral).mp ⟨f, hf0, hf⟩
  have hxP : IsIntegral ℚ[X] x := hxQ.tower_top
  obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℚ[X]) (K := RatFunc ℚ)).mp hxP
  have h1 : aeval (algebraMap ℚ[X] (RatFunc ℚ) g) f = algebraMap ℚ[X] (RatFunc ℚ) (f.comp g) := by
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) g f
    rw [Polynomial.comp_eq_aeval]
    exact this
  rw [← hg, h1, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ)), comp_eq_zero_iff] at hf
  rcases hf with hf | ⟨_, hgc⟩
  · exact hf0 hf
  · apply hnc (g.coeff 0)
    have hQK : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr hQ
    have h2 : x = algebraMap ℚ[X] (RatFunc ℚ) (C (g.coeff 0)) := by rw [← hg, ← hgc]
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    rw [map_mul, ← h2, div_mul_cancel₀ _ hQK]

/-- A copy of `FractionRing D` carrying no instances inherited from the algebra structures of
`D`. -/
def KSyn (D : Type) [CommRing D] [IsDomain D] : Type := FractionRing D

instance (D : Type) [CommRing D] [IsDomain D] : Field (KSyn D) :=
  inferInstanceAs (Field (FractionRing D))
instance (D : Type) [CommRing D] [IsDomain D] : Algebra D (KSyn D) :=
  inferInstanceAs (Algebra D (FractionRing D))
instance (D : Type) [CommRing D] [IsDomain D] : IsFractionRing D (KSyn D) :=
  inferInstanceAs (IsFractionRing D (FractionRing D))

/-- The identity `ℚ[X] → SrcPoly`. -/
def toSrc (f : ℚ[X]) : SrcPoly := f

/-- The construction behind `KummerCompositum`, from an abstract ring `D` (in the application
`D = (O ⊗_{ℚ[X]} B)/𝔫` for a minimal prime `𝔫`). -/
theorem kc_core (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (P Q : ℚ[X]) (s₀ : ℚ)
    (𝔓 : Ideal (integralClosure ℚ[X] E)) [h𝔓m : 𝔓.IsMaximal]
    (φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* AlgebraicClosure ℚ)
    (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra SrcPoly O]
    [hp0 : (Ideal.span {toSrc (X - C s₀)}).IsPrime]
    [IsLocalization.AtPrime O (Ideal.span {toSrc (X - C s₀)})]
    (ρ : ℚ[X] →+* O) (hρ : Function.Injective ρ)
    (oK : O →+* RatFunc ℚ)
    (hoK : ∀ a : SrcPoly, oK (algebraMap SrcPoly O a) = algebraMap ℚ[X] (RatFunc ℚ) a.toPoly)
    (hoKρX : oK (ρ X) = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q)
    (evO : O →+* ℚ) (hevO : ∀ o, evO o = 0 ↔ o ∈ maximalIdeal O)
    (D : Type) [CommRing D] [IsDomain D] (iO : O →+* D) (hiO : Function.Injective iO)
    (iB : integralClosure ℚ[X] E →+* D)
    (hiB : ∀ c : ℚ[X], iB (algebraMap ℚ[X] (integralClosure ℚ[X] E) c) = iO (ρ c))
    (hgen : ∀ d : D, d ∈ Subring.closure (Set.range iO ∪ Set.range iB))
    (hint : iO.IsIntegral)
    (N' : Ideal D) [hN' : N'.IsPrime] (hN'O : N'.comap iO = maximalIdeal O)
    (hN'B : 𝔓 ≤ N'.comap iB) :
    ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
      (ι : E →+* E'),
      KummerShape E E' ι (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) ∧
      Module.finrank (RatFunc ℚ) E' ≤ Module.finrank (RatFunc ℚ) E ∧
      ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
        𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
        ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* AlgebraicClosure ℚ,
          IntermediateField.adjoin ℚ (Set.range φ) ≤ IntermediateField.adjoin ℚ (Set.range φ') := by
  classical
  set p0 : Ideal SrcPoly := Ideal.span {toSrc (X - C s₀)} with hp0_def
  -- the maps into `E' = Frac D`
  let gO : O →+* KSyn D := (algebraMap D (KSyn D)).comp iO
  have hgO : Function.Injective gO := (IsFractionRing.injective D (KSyn D)).comp hiO
  let gS : ℚ[X] →+* KSyn D := gO.comp (algebraMap SrcPoly O)
  have hSO : Function.Injective (algebraMap SrcPoly O) :=
    IsLocalization.injective O p0.primeCompl_le_nonZeroDivisors
  have hgS : Function.Injective gS := fun a b h => hSO (hgO h)
  letI iK' : Algebra (RatFunc ℚ) (KSyn D) :=
    (IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) hgS).toAlgebra
  letI iP : Algebra ℚ[X] (KSyn D) :=
    ((algebraMap (RatFunc ℚ) (KSyn D)).comp (algebraMap ℚ[X] (RatFunc ℚ))).toAlgebra
  haveI iT : IsScalarTower ℚ[X] (RatFunc ℚ) (KSyn D) := IsScalarTower.of_algebraMap_eq' rfl
  have hPS : ∀ a : ℚ[X], algebraMap ℚ[X] (KSyn D) a = gS a := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) (KSyn D)]
    exact IsFractionRing.lift_algebraMap hgS a
  have hKO : ∀ o, algebraMap (RatFunc ℚ) (KSyn D) (oK o) = gO o := by
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp oK = gO := by
      apply IsLocalization.ringHom_ext p0.primeCompl
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply]
      rw [hoK]
      exact IsFractionRing.lift_algebraMap hgS a
    intro o
    exact RingHom.congr_fun this o
  -- `ι : E → E'`
  let ιB : integralClosure ℚ[X] E →+* KSyn D := (algebraMap D (KSyn D)).comp iB
  have hιB : Function.Injective ιB := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have hne := Ideal.under_ne_bot_of_integral_mem (R := ℚ[X]) hb0
      (Ideal.mem_span_singleton_self b) (Algebra.IsIntegral.isIntegral b)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hc
    have h1 : ιB (algebraMap ℚ[X] _ c) = 0 := by rw [← hb', map_mul, hb, mul_zero]
    change algebraMap D (KSyn D) (iB _) = 0 at h1
    rw [hiB] at h1
    exact hc0 (hρ (hgO (h1.trans (map_zero gO).symm) |>.trans (map_zero ρ).symm))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc ℚ) E
  let ι : E →+* KSyn D := IsFractionRing.lift hιB
  have hι : ∀ b, ι (algebraMap (integralClosure ℚ[X] E) E b) = ιB b :=
    fun b => IsFractionRing.lift_algebraMap hιB b
  have hιX : ι (algebraMap ℚ[X] E X) = gO (ρ X) := by
    rw [IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E, hι]
    change algebraMap D (KSyn D) (iB _) = _
    rw [hiB]
    rfl
  have hshape1 : ι (algebraMap (RatFunc ℚ) E RatFunc.X) = algebraMap (RatFunc ℚ) (KSyn D)
      (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) := by
    rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, hιX,
      ← hoKρX, hKO]
  -- the subfield generated by `ι(E)` and `s` is everything
  set F := Subfield.closure (Set.range ι ∪ {algebraMap (RatFunc ℚ) (KSyn D) RatFunc.X}) with hF
  have hK'F : ∀ z : RatFunc ℚ, algebraMap (RatFunc ℚ) (KSyn D) z ∈ F := by
    intro z
    have h1 : Subfield.closure {(RatFunc.X : RatFunc ℚ)} ≤ F.comap (algebraMap (RatFunc ℚ) (KSyn D)) := by
      rw [Subfield.closure_le]
      rintro _ rfl
      exact Subfield.subset_closure (Or.inr rfl)
    exact h1 (ratFunc_mem_closure z)
  have hDF : ∀ d : D, algebraMap D (KSyn D) d ∈ F := by
    intro d
    induction hgen d using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨o, rfl⟩ | ⟨b, rfl⟩
      · change gO o ∈ F
        rw [← hKO]; exact hK'F _
      · change ιB b ∈ F
        rw [← hι]; exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact one_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hFtop : F = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := D) z
    exact div_mem (hDF a) (hDF b)
  -- `κ : ℚ(X) → ℚ(s)`, `X ↦ P/Q`, compatible with `ι`
  have hκg : Function.Injective (oK.comp ρ) := by
    intro a b h
    apply hρ
    apply hgO
    rw [← hKO, ← hKO]
    exact congrArg (algebraMap (RatFunc ℚ) (KSyn D)) h
  let κ : RatFunc ℚ →+* RatFunc ℚ := IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) hκg
  have hκ : ∀ k, algebraMap (RatFunc ℚ) (KSyn D) (κ k) = ι (algebraMap (RatFunc ℚ) E k) := by
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp κ = ι.comp (algebraMap (RatFunc ℚ) E) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
      apply RingHom.ext
      intro f
      simp only [RingHom.comp_apply]
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply, hKO,
        ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E, hι]
      change gO (ρ f) = algebraMap D (KSyn D) (iB _)
      rw [hiB]
      rfl
    intro k
    exact RingHom.congr_fun this k
  -- a primitive element
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (RatFunc ℚ) E
  have hθint : IsIntegral (RatFunc ℚ) θ := .of_finite _ _
  set m := minpoly (RatFunc ℚ) θ
  have hroot : aeval (ι θ) (m.map κ) = 0 := by
    rw [aeval_def, eval₂_map]
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp κ = ι.comp (algebraMap (RatFunc ℚ) E) :=
      RingHom.ext hκ
    rw [this, ← Polynomial.hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hmon : (m.map κ).Monic := (minpoly.monic hθint).map κ
  have hιθint : IsIntegral (RatFunc ℚ) (ι θ) := ⟨_, hmon, hroot⟩
  -- `E' = ℚ(s)(ι θ)`
  have hadjtop : IntermediateField.adjoin (RatFunc ℚ) {ι θ} = ⊤ := by
    set L' := IntermediateField.adjoin (RatFunc ℚ) {ι θ}
    have hrange : ∀ e : E, ι e ∈ L' := by
      intro e
      have hle : (IntermediateField.adjoin (RatFunc ℚ) {θ}).toSubfield ≤
          L'.toSubfield.comap ι := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro _ (⟨k, rfl⟩ | h)
        · change ι (algebraMap (RatFunc ℚ) E k) ∈ L'
          rw [← hκ]; exact L'.algebraMap_mem _
        · rw [Set.mem_singleton_iff] at h
          subst h
          exact IntermediateField.mem_adjoin_simple_self _ _
      have he : e ∈ (IntermediateField.adjoin (RatFunc ℚ) {θ}).toSubfield := by
        rw [hθ]; trivial
      exact hle he
    have hFle : F ≤ L'.toSubfield := by
      rw [hF, Subfield.closure_le]
      rintro _ (⟨e, rfl⟩ | h)
      · exact hrange e
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact L'.algebraMap_mem _
    rw [eq_top_iff]
    intro z _
    exact hFle (hFtop ▸ Subfield.mem_top z)
  haveI hfd : FiniteDimensional (RatFunc ℚ) (KSyn D) := by
    have h1 := IntermediateField.adjoin.finiteDimensional hιθint
    rw [hadjtop] at h1
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  have hfin : Module.finrank (RatFunc ℚ) (KSyn D) ≤ Module.finrank (RatFunc ℚ) E := by
    rw [← IntermediateField.finrank_top', ← hadjtop, IntermediateField.adjoin.finrank hιθint,
      ← IntermediateField.finrank_top' (F := RatFunc ℚ) (E := E), ← hθ,
      IntermediateField.adjoin.finrank hθint]
    calc (minpoly (RatFunc ℚ) (ι θ)).natDegree ≤ (m.map κ).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hmon.ne_zero
      _ = m.natDegree := natDegree_map κ
  -- the integral closure `C` of `O` in `E'` and a prime `𝔐` of `C` over `N'`
  letI iOE : Algebra O (KSyn D) := gO.toAlgebra
  letI iOD : Algebra O D := iO.toAlgebra
  haveI : IsScalarTower O D (KSyn D) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral O D := ⟨hint⟩
  let jD : D →ₐ[O] integralClosure O (KSyn D) :=
    (IsScalarTower.toAlgHom O D (KSyn D)).codRestrict (integralClosure O (KSyn D))
      (fun d => (Algebra.IsIntegral.isIntegral (R := O) d).map (IsScalarTower.toAlgHom O D (KSyn D)))
  have hjD : Function.Injective jD := by
    intro x y h
    exact IsFractionRing.injective D (KSyn D) (congrArg Subtype.val h)
  letI iDC : Algebra D (integralClosure O (KSyn D)) := jD.toRingHom.toAlgebra
  haveI : IsScalarTower O D (integralClosure O (KSyn D)) :=
    IsScalarTower.of_algebraMap_eq (fun o => (jD.commutes o).symm)
  haveI : Algebra.IsIntegral D (integralClosure O (KSyn D)) :=
    Algebra.IsIntegral.tower_top O
  have hkerD : (⊥ : Ideal (integralClosure O (KSyn D))).under D ≤ N' := by
    intro x hx
    have : jD x = 0 := hx
    rw [hjD (this.trans (map_zero jD).symm)]
    exact N'.zero_mem
  obtain ⟨𝔐, -, h𝔐p, h𝔐⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure O (KSyn D)) N' ⊥ hkerD
  have hmem𝔐 : ∀ d : D, jD d ∈ 𝔐 ↔ d ∈ N' := by
    intro d
    rw [← h𝔐]
    rfl
  -- `B' ⊆ C`
  let sO : ℚ[X] →+* O := algebraMap SrcPoly O
  have hintB' : ∀ x : KSyn D, IsIntegral ℚ[X] x → IsIntegral O x := by
    intro x ⟨p, hp, hpx⟩
    refine ⟨p.map sO, hp.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap O (KSyn D)).comp sO = algebraMap ℚ[X] (KSyn D) :=
      RingHom.ext fun a => (hPS a).symm
    rw [this]; exact hpx
  let jB : integralClosure ℚ[X] (KSyn D) →+* integralClosure O (KSyn D) :=
    { toFun := fun x => ⟨x.1, hintB' x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hjBalg : ∀ a : ℚ[X], jB (algebraMap ℚ[X] _ a) =
      jD (iO (algebraMap SrcPoly O a)) := by
    intro a
    apply Subtype.ext
    change algebraMap ℚ[X] (KSyn D) a = gO (algebraMap SrcPoly O a)
    exact hPS a
  set 𝔓' := 𝔐.comap jB with h𝔓'_def
  haveI : 𝔓'.IsPrime := Ideal.IsPrime.comap jB
  have hunder : 𝔓'.under ℚ[X] = Ideal.span {X - C s₀} := by
    ext a
    change jB (algebraMap ℚ[X] _ a) ∈ 𝔐 ↔ _
    rw [hjBalg, hmem𝔐, ← Ideal.mem_comap, hN'O]
    change algebraMap SrcPoly O (toSrc a) ∈ maximalIdeal O ↔ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O p0]
    rfl
  sorry


theorem kummerCompositum_proof : KummerCompositum := by
  intro E _ _ _ _ _ P Q t s₀ hQ hPQ hnc 𝔓 h𝔓 h𝔓u φ
  classical
  -- the `s`-coordinate local ring `O = ℚ[s]_(s - s₀)` (as a localization of `SrcPoly`)
  set p0 : Ideal SrcPoly := Ideal.span {toSrc (X - C s₀)} with hp0_def
  haveI hp0 : p0.IsPrime := by
    change (Ideal.span {(X - C s₀ : ℚ[X])}).IsPrime
    exact (Ideal.span_singleton_prime (X_sub_C_ne_zero s₀)).mpr (prime_X_sub_C s₀)
  have hmem0 : ∀ f : SrcPoly, f ∈ p0 ↔ f.toPoly.eval s₀ = 0 := by
    intro f
    change (f.toPoly ∈ Ideal.span {(X - C s₀ : ℚ[X])}) ↔ _
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
    rfl
  set O := Localization.AtPrime p0
  let ev0 : SrcPoly →+* ℚ := (Polynomial.evalRingHom s₀ : ℚ[X] →+* ℚ)
  have hev0 : ∀ f : SrcPoly, ev0 f = f.toPoly.eval s₀ := fun f => rfl
  have hunit0 : ∀ y : p0.primeCompl, IsUnit (ev0 y) := fun y =>
    Ne.isUnit (by rw [hev0]; exact fun h => y.2 ((hmem0 _).mpr h))
  let evO : O →+* ℚ := IsLocalization.lift (M := p0.primeCompl) (S := O) (g := ev0) hunit0
  have hevO : ∀ f : SrcPoly, evO (algebraMap SrcPoly O f) = f.toPoly.eval s₀ :=
    fun f => IsLocalization.lift_eq hunit0 f
  have hQ0 : toSrc Q ∉ p0 := fun h => hQ ((hmem0 _).mp h)
  set r : O := IsLocalization.mk' O (toSrc P) (⟨toSrc Q, hQ0⟩ : p0.primeCompl) with hr_def
  have hrspec : r * algebraMap SrcPoly O (toSrc Q) = algebraMap SrcPoly O (toSrc P) :=
    IsLocalization.mk'_spec O _ _
  have hevr : evO r = t := by
    have h1 := congrArg evO hrspec
    rw [map_mul, hevO, hevO] at h1
    change evO r * Q.eval s₀ = P.eval s₀ at h1
    rw [hPQ] at h1
    exact mul_right_cancel₀ hQ h1
  let Csrc : ℚ →+* SrcPoly := (Polynomial.C : ℚ →+* ℚ[X])
  let ρ : ℚ[X] →+* O := Polynomial.eval₂RingHom ((algebraMap SrcPoly O).comp Csrc) r
  have hevρ : ∀ f : ℚ[X], evO (ρ f) = f.eval t := by
    have : evO.comp ρ = Polynomial.evalRingHom t := by
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_rat ((evO.comp ρ).comp C)
          ((Polynomial.evalRingHom t).comp C)) a
      · simp only [RingHom.comp_apply, coe_evalRingHom, eval_X]
        change evO (eval₂ _ r X) = t
        rw [eval₂_X, hevr]
    intro f
    exact RingHom.congr_fun this f
  letI : Algebra ℚ[X] O := ρ.toAlgebra
  -- `(integralClosure ℚ[X] E)` and the residue field at `𝔓`
  haveI := h𝔓
  let χ0 : O →+* (integralClosure ℚ[X] E) ⧸ 𝔓 := ((algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓)).comp C).comp evO
  have hχ0 : ∀ f : ℚ[X], χ0 (ρ f) = algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓) f := by
    intro f
    change algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓) (C (evO (ρ f))) = _
    rw [hevρ, ← sub_eq_zero, ← map_sub,
      IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) ((integralClosure ℚ[X] E) ⧸ 𝔓), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
    change _ ∈ 𝔓.under ℚ[X]
    rw [h𝔓u, Ideal.mem_span_singleton, ← dvd_neg, neg_sub]
    exact X_sub_C_dvd_sub_C_eval
  let χ : O →ₐ[ℚ[X]] (integralClosure ℚ[X] E) ⧸ 𝔓 := { χ0 with commutes' := hχ0 }
  -- the tensor product `T = O ⊗_{ℚ[X]} (integralClosure ℚ[X] E)` and the prime `N` over `𝔓` and `max O`
  let ψ0 : O ⊗[ℚ[X]] (integralClosure ℚ[X] E) →ₐ[ℚ[X]] (integralClosure ℚ[X] E) ⧸ 𝔓 :=
    Algebra.TensorProduct.lift χ (Ideal.Quotient.mkₐ ℚ[X] 𝔓) (fun x y => Commute.all (χ x) (Ideal.Quotient.mkₐ ℚ[X] 𝔓 y))
  set N := RingHom.ker ψ0.toRingHom
  haveI : N.IsPrime := RingHom.ker_isPrime _
  obtain ⟨𝔫, h𝔫min, h𝔫N⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (O ⊗[ℚ[X]] (integralClosure ℚ[X] E))))
    (J := N) bot_le
  haveI h𝔫p : 𝔫.IsPrime := h𝔫min.1.1
  -- `T` is free over `O`
  have hinjE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : Module.IsTorsionFree ℚ[X] E := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjE
  haveI : Algebra.IsSeparable (RatFunc ℚ) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Free ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.module_free ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Free O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := inferInstance
  haveI : Module.IsTorsionFree O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := inferInstance
  have hdisj : ∀ o : O, o ≠ 0 → algebraMap O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) o ∉ 𝔫 := by
    intro o ho hm
    have hnzd : algebraMap O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) o ∈ nonZeroDivisors (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      rw [mul_comm, ← Algebra.smul_def] at hx
      exact (smul_eq_zero_iff_right ho).mp hx
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔫min) hm hnzd
  -- the map `O → ℚ(s)` and injectivity of `ρ`
  let sK : SrcPoly →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)
  have hS_K : ∀ y : p0.primeCompl, IsUnit (sK y) := by
    intro y
    refine Ne.isUnit fun h0 => y.2 ?_
    have : (y : SrcPoly) = 0 := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
      (h0.trans (map_zero sK).symm)
    rw [this]; exact p0.zero_mem
  let oK : O →+* RatFunc ℚ := IsLocalization.lift (M := p0.primeCompl) (S := O) (g := sK) hS_K
  have hoK : ∀ a : SrcPoly, oK (algebraMap SrcPoly O a) = algebraMap ℚ[X] (RatFunc ℚ) a.toPoly :=
    fun a => IsLocalization.lift_eq hS_K a
  have hQK : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
      (fun h0 => hQ (by rw [h0, eval_zero]))
  have hoKr : oK r = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q := by
    have h1 := congrArg oK hrspec
    rw [map_mul, hoK, hoK] at h1
    rw [eq_div_iff hQK]; exact h1
  have hoKρ : ∀ f : ℚ[X], oK (ρ f) =
      aeval (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) f := by
    have : oK.comp ρ = (aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_rat ((oK.comp ρ).comp C)
          (((aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
            algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom).comp C)) a
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        change oK (eval₂ _ r X) = _
        rw [eval₂_X, hoKr]
    intro f
    exact RingHom.congr_fun this f
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have := hoKρ f
    rw [hf, map_zero] at this
    exact ratFunc_transc P Q (fun h0 => hQ (by rw [h0, eval_zero])) hnc f this.symm
  sorry

end TsKummer
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.compositum_core0
#print axioms TsKummer.kummerOtherBranchFin_of_unram
#print axioms TsKummer.unramCompositum
#print axioms TsKummer.kummerOtherBranchInf_of_unram
#print axioms TsKummer.unramBaseChange
#print axioms TsKummer.kummerVerticalFin_proof
#print axioms TsKummer.kummerVerticalInf_proof
