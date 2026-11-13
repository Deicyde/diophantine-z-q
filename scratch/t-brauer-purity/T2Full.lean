import Mathlib

/-!
# t-brauer-purity: Abhyankar's lemma, DVR form (leaf T2, `PkgI2.AbhyankarDVR`), full proof attempt

Contents: copies of `AbhyankarBricks.lean` and `KummerUnramified.lean` (scratch files cannot import
each other), then the assembly following docs/research/t-brauer-purity.md §4.
-/

/-!
# t-brauer-purity: the unit-radicand Kummer step of Abhyankar's lemma is unramified

Step (b) of the proof of leaf T2 (`PkgI2.AbhyankarDVR`, docs/research/t-brauer-purity.md §2, §4):
adjoining an `e`-th root `w` of an element `u` of a Dedekind domain `A`, with `e` invertible, gives
an extension unramified at every prime `P` of the integral closure `B` with `u ∉ P`.

Proof: if `P` were ramified it would divide the different ideal (`dvd_differentIdeal_iff`), which
contains `g'(w)` for `g` the minimal polynomial of `w` (`aeval_derivative_mem_differentIdeal`).
`g ∣ Xᵉ - u` gives `e wᵉ⁻¹ = g'(w) h(w) ∈ P`, hence `wᵉ = u ∈ P`.
-/

open Polynomial

namespace TBrauerPurity

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem isUnramifiedAt_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : Algebra.IsUnramifiedAt A P := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv B L).symm _
  by_contra hP
  rw [← dvd_differentIdeal_iff] at hP
  have hle : differentIdeal A B ≤ P := Ideal.le_of_dvd hP
  have hmem := hle (aeval_derivative_mem_differentIdeal A K L w hgen)
  have hint : IsIntegral A w := IsIntegralClosure.isIntegral A L w
  have haev : aeval w (X ^ e - C u) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint haev
  have hder : aeval w (derivative (X ^ e - C u)) =
      aeval w (derivative (minpoly A w)) * aeval w h := by
    rw [hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  have hin : aeval w (derivative (X ^ e - C u : A[X])) ∈ P := by
    rw [hder]; exact P.mul_mem_right _ hmem
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, aeval_C, map_pow,
    aeval_X] at hin
  have heB : IsUnit (algebraMap A B (e : A)) := he.map _
  have hpow : w ^ (e - 1) ∈ P := by
    rcases (Ideal.IsPrime.mem_or_mem ‹_› hin) with h1 | h1
    · rw [map_natCast] at h1 heB
      exact absurd (P.eq_top_of_isUnit_mem h1 heB) (Ideal.IsPrime.ne_top ‹_›)
    · exact h1
  apply hu
  rw [← hw, show e = (e - 1) + 1 by omega, pow_succ]
  exact P.mul_mem_right _ hpow

/-- Corollary: ramification index one at such `P`. -/
theorem ramificationIdx_eq_one_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : P.ramificationIdx A = 1 := by
  have := isUnramifiedAt_of_pow_eq A K L B e he0 he w u hw hgen P hu
  exact Ideal.ramificationIdx_eq_one P A

end TBrauerPurity


/-!
# t-brauer-purity: bricks toward Abhyankar's lemma (leaf T2, `PkgI2.AbhyankarDVR`)

In the setting of `PkgI2.AbhyankarDVR` (scratch/h-decomposition/Leaves.lean, ZInQKernel/HDecomp/
Objects.lean), with the same instance context:

* `abhyankar_finiteDimensional`, `abhyankar_isSeparable`: `M = L(t)`, `tⁿ = π`, `n` invertible in
  `R`, force `M/K` finite separable, so `integralClosure R M` is a Dedekind domain
  (`abhyankar_isDedekindDomain`).
* `dvd_ramificationIdx_of_pow_eq` (general): over a DVR `R` with uniformizer `π`, if `tⁿ = π` in a
  Dedekind `R`-algebra `S` with `𝔪S ≠ ⊥`, then `n` divides the ramification index of every prime of
  `S` over `𝔪`.
* `abhyankar_dvd_ramificationIdx`: hence in the leaf's setting `n ∣ e(Q | 𝔪)` for every prime `Q` of
  `integralClosure R M` over `𝔪`: the lower half of the leaf's conclusion `e(Q | 𝔪) = n`
  (the upper half `e ≤ n` and the residue separability need the local Kummer analysis and remain
  open; see docs/research/t-brauer-purity.md).
-/

open Polynomial IsLocalRing

namespace TBrauerPurity

/-- **General divisibility.** `R` a DVR with uniformizer `π`, `S` a Dedekind domain over `R` with
`𝔪S ≠ ⊥`, and `t ∈ S` with `tⁿ = π`: every prime `Q` of `S` over `𝔪` has `n ∣ e(Q|𝔪)`. -/
theorem dvd_ramificationIdx_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    {π : R} (hπ : Irreducible π) (n : ℕ) (t : S) (ht : t ^ n = algebraMap R S π)
    (Q : Ideal S) [Q.LiesOver (maximalIdeal R)]
    (h0 : (maximalIdeal R).map (algebraMap R S) ≠ ⊥) :
    n ∣ Q.ramificationIdx R := by
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (maximalIdeal R) Q h0]
  have hm : (maximalIdeal R).map (algebraMap R S) = Ideal.span {t} ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
      Set.image_singleton, ← ht, Ideal.span_singleton_pow]
  rw [hm, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
  exact dvd_mul_right _ _

section Setting

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (R K L M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]

include K in
/-- The tower `R → L → M` commutes in the leaf's setting. -/
theorem abhyankar_isScalarTower_RLM : IsScalarTower R L M := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply R K L,
    IsScalarTower.algebraMap_apply K L M]

variable {R K L M}

include K in
/-- `π ≠ 0` and `n ≠ 0` in `L` for a uniformizer `π` and `n` invertible in `R`. -/
lemma abhyankar_ne_zero {π : R} (hπ : Irreducible π) {n : ℕ} (hn : IsUnit (n : R)) :
    algebraMap R L π ≠ 0 ∧ (n : L) ≠ 0 := by
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  refine ⟨fun h => hπ.ne_zero (hinj (by rw [h, map_zero])), fun h => ?_⟩
  have := hn.map (algebraMap R L)
  rw [map_natCast, h] at this
  exact not_isUnit_zero this

include K in
/-- `t` is a root of the separable polynomial `Xⁿ - π` over `L`. -/
lemma abhyankar_aeval {π : R} {n : ℕ} {t : M} (ht : t ^ n = algebraMap R M π) :
    aeval t (X ^ n - C (algebraMap R L π)) = 0 := by
  haveI := abhyankar_isScalarTower_RLM R K L M
  rw [map_sub, map_pow, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, ht, sub_self]

include K in
/-- `M` is finite over `L` (hence over `K`). -/
theorem abhyankar_finiteDimensional_L {π : R} {n : ℕ} (hn0 : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    FiniteDimensional L M := by
  have hint : IsIntegral L t :=
    ⟨X ^ n - C (algebraMap R L π), monic_X_pow_sub_C _ hn0.ne', by
      rw [← aeval_def]; exact abhyankar_aeval (K := K) ht⟩
  haveI := IntermediateField.adjoin.finiteDimensional hint
  exact LinearEquiv.finiteDimensional
    ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).toLinearEquiv

theorem abhyankar_finiteDimensional {π : R} {n : ℕ} (hn0 : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    FiniteDimensional K M := by
  haveI := abhyankar_finiteDimensional_L (K := K) hn0 ht hM
  exact Module.Finite.trans L M

/-- `M/K` is separable. -/
theorem abhyankar_isSeparable {π : R} (hπ : Irreducible π) {n : ℕ} (hn : IsUnit (n : R))
    {t : M} (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤) :
    Algebra.IsSeparable K M := by
  obtain ⟨hπ0, hn0⟩ := abhyankar_ne_zero (L := L) (K := K) hπ hn
  have hsep : IsSeparable L t :=
    (separable_X_pow_sub_C _ hn0 hπ0).of_dvd (minpoly.dvd L t (abhyankar_aeval (K := K) ht))
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable L M).mpr hsep
  haveI : Algebra.IsSeparable L M := Algebra.IsSeparable.of_algHom L
    (IntermediateField.adjoin L {t})
    ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).symm.toAlgHom
  exact Algebra.IsSeparable.trans K L M

include K in
/-- `integralClosure R M` is a Dedekind domain. -/
theorem abhyankar_isDedekindDomain {π : R} (hπ : Irreducible π) {n : ℕ} (hn0 : 0 < n)
    (hn : IsUnit (n : R)) {t : M} (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin L {t} = ⊤) :
    IsDedekindDomain (integralClosure R M) := by
  haveI := abhyankar_finiteDimensional (K := K) hn0 ht hM
  haveI := abhyankar_isSeparable (K := K) hπ hn ht hM
  exact integralClosure.isDedekindDomain R K M

include K in
/-- **Lower half of the conclusion of `PkgI2.AbhyankarDVR`.** In the leaf's setting (and under
its hypotheses on `π`, `n`, `t`; the tameness hypothesis on `L` is not needed for this half),
every prime `Q` of `integralClosure R M` over `𝔪` has `n ∣ e(Q | 𝔪)`. -/
theorem abhyankar_dvd_ramificationIdx (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n)
    (hn : IsUnit (n : R)) (t : M) (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin L {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    n ∣ Q.ramificationIdx R := by
  haveI := abhyankar_isDedekindDomain (K := K) hπ hn0 hn ht hM
  have htint : IsIntegral R t :=
    ⟨X ^ n - C π, monic_X_pow_sub_C _ hn0.ne', by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, ht, sub_self]⟩
  let t' : integralClosure R M := ⟨t, htint⟩
  have ht' : t' ^ n = algebraMap R (integralClosure R M) π := Subtype.ext ht
  refine dvd_ramificationIdx_of_pow_eq hπ n t' ht' Q ?_
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
    Set.image_singleton, Ne, Ideal.span_singleton_eq_bot, ← ht']
  intro h
  have h2 : t ^ n = 0 := congrArg Subtype.val h
  rw [ht] at h2
  obtain ⟨hπ0, -⟩ := abhyankar_ne_zero (L := L) (K := K) hπ hn
  apply hπ0
  haveI := abhyankar_isScalarTower_RLM R K L M
  rw [IsScalarTower.algebraMap_apply R L M] at h2
  exact (algebraMap L M).injective (by rw [h2, map_zero])

end Setting

section KummerUniformizer

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {R K M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]

/-- `[K(t) : K] ≤ m` for a root `t` of `Xᵐ - π`. -/
lemma finrank_le_of_pow_eq {π : R} {m : ℕ} (hm0 : 0 < m) {t : M}
    (ht : t ^ m = algebraMap R M π) (hM : IntermediateField.adjoin K {t} = ⊤) :
    Module.finrank K M ≤ m := by
  have haev : aeval t (X ^ m - C (algebraMap R K π)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, ht, sub_self]
  have hmon : (X ^ m - C (algebraMap R K π)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hint : IsIntegral K t := ⟨_, hmon, by rw [← aeval_def]; exact haev⟩
  rw [← ((IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank hint]
  calc (minpoly K t).natDegree ≤ (X ^ m - C (algebraMap R K π)).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd K t haev) hmon.ne_zero
    _ = m := natDegree_X_pow_sub_C

/-- **Abhyankar's lemma for `L = K`, i.e. a Kummer extension by an `m`-th root of a uniformizer
is totally ramified.** `R` a DVR with fraction field `K` and uniformizer `π`, `m ≥ 1` invertible in
`R`, `M = K(t)` with `tᵐ = π`.  Every prime `Q` of `integralClosure R M` over `𝔪` has
`e(Q|𝔪) = m` and `f(Q|𝔪) = 1` (so its residue field is `R/𝔪`, trivially separable). -/
theorem ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq (π : R) (hπ : Irreducible π) (m : ℕ)
    (hm0 : 0 < m) (hm : IsUnit (m : R)) (t : M) (ht : t ^ m = algebraMap R M π)
    (hM : IntermediateField.adjoin K {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    Q.ramificationIdx R = m ∧ Q.inertiaDeg R = 1 := by
  haveI := abhyankar_isDedekindDomain (R := R) (K := K) (L := K) hπ hm0 hm ht hM
  haveI := abhyankar_finiteDimensional (R := R) (K := K) (L := K) hm0 ht hM
  haveI := abhyankar_isSeparable (R := R) (K := K) (L := K) hπ hm ht hM
  have hdvd := abhyankar_dvd_ramificationIdx (R := R) (K := K) (L := K) π hπ m hm0 hm t ht hM Q
  haveI : Module.Finite R (integralClosure R M) := IsIntegralClosure.finite R K M _
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective R K)
  haveI : Module.IsTorsionFree R (integralClosure R M) := inferInstance
  have hrank : Module.finrank R (integralClosure R M) = Module.finrank K M :=
    IsIntegralClosure.rank R K M _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal R) (integralClosure R M)
  rw [hrank] at hsum
  have hle := finrank_le_of_pow_eq (K := K) hm0 ht hM
  have hQ : Q.ramificationIdx R * Q.inertiaDeg R ≤ m := by
    refine le_trans ?_ (hsum.trans_le hle)
    exact Finset.single_le_sum (f := fun q : (maximalIdeal R).primesOver (integralClosure R M) =>
        q.1.ramificationIdx R * q.1.inertiaDeg R) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Ideal.primesOver.mk (maximalIdeal R) Q))
  have he0 : 0 < Q.ramificationIdx R := Ideal.ramificationIdx_pos R Q
  have hf0 : 0 < Q.inertiaDeg R := Ideal.inertiaDeg_pos Q R
  have hem : m ≤ Q.ramificationIdx R := Nat.le_of_dvd he0 hdvd
  constructor
  · nlinarith
  · nlinarith

/-- **`PkgI2.AbhyankarDVR`'s conclusion in the case `L = K`** (the leaf's exact conclusion:
ramification index `n` and separable residue extension, with the leaf's quotient algebra
instance). -/
theorem abhyankarDVR_conclusion_of_L_eq_K (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n)
    (hn : IsUnit (n : R)) (t : M) (ht : t ^ n = algebraMap R M π)
    (hM : IntermediateField.adjoin K {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    Q.ramificationIdx R = n ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q) := by
  obtain ⟨he, hf⟩ := ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq π hπ n hn0 hn t ht hM Q
  refine ⟨he, ?_⟩
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) Q] at hf
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  letI : Field (integralClosure R M ⧸ Q) := Ideal.Quotient.field _
  haveI : Module.Free (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q) :=
    Module.Free.of_divisionRing _ _
  have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one (F := R ⧸ maximalIdeal R)
    (E := integralClosure R M ⧸ Q)).mpr hf
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q)) := by
    rw [hbot]; trivial
  obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx
  exact isSeparable_algebraMap y

end KummerUniformizer

section Assembly

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IntermediateField

/-- `[F(t) : F] ≤ m` for a root `t` of `Xᵐ - c`, `c ∈ F`. -/
lemma finrank_le_of_pow_eq_field {F E : Type*} [Field F] [Field E] [Algebra F E] {m : ℕ}
    (hm0 : 0 < m) {t : E} {c : F} (ht : t ^ m = algebraMap F E c)
    (hE : IntermediateField.adjoin F {t} = ⊤) : Module.finrank F E ≤ m := by
  have haev : aeval t (X ^ m - C c) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ht, sub_self]
  have hmon : (X ^ m - C c).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hint : IsIntegral F t := ⟨_, hmon, by rw [← aeval_def]; exact haev⟩
  rw [← ((IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank hint]
  calc (minpoly F t).natDegree ≤ (X ^ m - C c).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd F t haev) hmon.ne_zero
    _ = m := natDegree_X_pow_sub_C

/-- `Algebra.adjoin F {x} = ⊤` inside `F⟮x⟯` for integral `x`. -/
lemma algebra_adjoin_gen_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E}
    (hx : IsIntegral F x) :
    Algebra.adjoin F {(⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯)} = ⊤ := by
  apply Subalgebra.map_injective (f := (F⟮x⟯).val) (F⟮x⟯).val.injective
  rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, IntermediateField.range_val,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic]
  rfl

/-- **Step (a).** In a Dedekind domain `A` integral over the DVR `R`, for a prime `Q` over `𝔪` with
ramification index `e`, the uniformizer factors as `π = u ϖᵉ` with `u ∉ Q`. -/
lemma exists_pow_mul_eq (R A : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    [Module.IsTorsionFree R A] (π : R) (hπ : Irreducible π) (Q : Ideal A) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ ϖ u : A, ϖ ≠ 0 ∧ algebraMap R A π = u * ϖ ^ (Q.ramificationIdx R) ∧ u ∉ Q := by
  sorry

theorem abhyankarDVR_main (R K L M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn0 : 0 < n) (hn : IsUnit (n : R))
    (htame : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime]
      [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q))
    (t : M) (ht : t ^ n = algebraMap R M π) (hM : IntermediateField.adjoin L {t} = ⊤)
    (Q' : Ideal (integralClosure R M)) [Q'.IsPrime]
    [Q'.LiesOver (IsLocalRing.maximalIdeal R)] :
    Q'.ramificationIdx R = n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q') := by
  haveI := abhyankar_isScalarTower_RLM R K L M
  haveI : FiniteDimensional L M := abhyankar_finiteDimensional_L (K := K) hn0 ht hM
  haveI : FiniteDimensional K M := abhyankar_finiteDimensional (K := K) hn0 ht hM
  haveI : Algebra.IsSeparable K M := abhyankar_isSeparable (K := K) hπ hn ht hM
  haveI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  -- the inclusion `S_L → S_M`
  let ι13 : integralClosure R L →ₐ[R] integralClosure R M :=
    ((IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val).codRestrict _
      (fun x => x.2.map (IsScalarTower.toAlgHom R L M))
  letI : Algebra (integralClosure R L) (integralClosure R M) := ι13.toAlgebra
  haveI : IsScalarTower R (integralClosure R L) (integralClosure R M) := IsScalarTower.of_algHom ι13
  let Q : Ideal (integralClosure R L) := Q'.under (integralClosure R L)
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.tower_bot Q' Q (IsLocalRing.maximalIdeal R)
  obtain ⟨heU, ⟨m, hm⟩, hsepQ⟩ := htame Q
  set e := Q.ramificationIdx R with he_def
  have he0 : 0 < e := Ideal.ramificationIdx_pos R Q
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  haveI : Module.IsTorsionFree R (integralClosure R L) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    apply (IsFractionRing.injective R K)
    apply (algebraMap K L).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact congrArg Subtype.val hab
  obtain ⟨ϖ, u, hϖ0, hπu, huQ⟩ := exists_pow_mul_eq R (integralClosure R L) π hπ Q
  rw [← he_def] at hπu
  -- `w = t^m / ϖ`, with `wᵉ = u`
  let ϖM : M := algebraMap L M ((ϖ : integralClosure R L) : L)
  have hϖM : ϖM ≠ 0 := by
    simp only [ϖM, ne_eq, map_eq_zero]
    exact fun h => hϖ0 (Subtype.ext h)
  let w : M := t ^ m / ϖM
  have hw : w ^ e = algebraMap L M ((u : integralClosure R L) : L) := by
    have h1 : t ^ (e * m) = algebraMap L M ((u : integralClosure R L) : L) * ϖM ^ e := by
      rw [← hm, ht, IsScalarTower.algebraMap_apply R L M]
      have : algebraMap R L π = ((algebraMap R (integralClosure R L) π : integralClosure R L) : L) :=
        rfl
      rw [this, hπu]
      simp [ϖM, map_mul, map_pow]
    simp only [w, div_pow, ← pow_mul, mul_comm m e, h1]
    field_simp
  sorry

end Assembly

end TBrauerPurity

