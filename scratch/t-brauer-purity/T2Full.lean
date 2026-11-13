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

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

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
    ∃ ϖ b a : A, ϖ ≠ 0 ∧ b ∉ Q ∧ a ∉ Q ∧
      b * algebraMap R A π = ϖ ^ (Q.ramificationIdx R) * a := by
  set e := Q.ramificationIdx R
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hπA : algebraMap R A π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R A) = Ideal.span {algebraMap R A π} := by
    rw [hm, Ideal.map_span, Set.image_singleton]
  have hmap0 : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hπA
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have h1 : (IsLocalRing.maximalIdeal R) = Q.under R := Q.over_def _
    rw [h] at h1
    change _ = Ideal.comap _ ⊥ at h1
    rw [Ideal.comap_bot_of_injective _ hinj, hm, Ideal.span_singleton_eq_bot] at h1
    exact hπ.ne_zero h1
  have hQ1 : Q ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQ0 ‹_›).irreducible
  -- `count_Q (π) = e`
  have hcount : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {algebraMap R A π})).count Q = e := by
    rw [← hmap]
    exact (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ Q hmap0).symm
  have hle : Ideal.span {algebraMap R A π} ≤ Q ^ e := by
    have h1 := Ideal.le_pow_ramificationIdx' (p := IsLocalRing.maximalIdeal R) (P := Q)
    have hm0 : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      rw [hm, Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
    rwa [Ideal.ramificationIdx'_eq_ramificationIdx _ Q hm0, hmap] at h1
  have hnle : ¬ Ideal.span {algebraMap R A π} ≤ Q ^ (e + 1) := by
    intro h
    have hd : Q ^ (e + 1) ∣ Ideal.span {algebraMap R A π} := Ideal.dvd_iff_le.mpr h
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero _ hQ0) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])] at hd
    have := Multiset.count_le_of_le Q hd
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQirr, normalize_eq,
      Multiset.count_nsmul, Multiset.count_singleton_self, hcount] at this
    omega
  -- a local uniformizer `ϖ ∈ Q \ Q²`
  obtain ⟨ϖ, hϖQ, hϖQ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q hQ0 hQ1 1
  rw [pow_one] at hϖQ
  have hϖ0 : ϖ ≠ 0 := fun h => hϖQ2 (h ▸ Ideal.zero_mem _)
  obtain ⟨J2, hJ2⟩ : Q ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖQ)
  have hJ2Q : ¬ J2 ≤ Q := by
    intro h
    apply hϖQ2
    have : Ideal.span {ϖ} ≤ Q ^ (1 + 1) := by
      rw [hJ2, pow_two]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  have hJ2eQ : ¬ J2 ^ e ≤ Q := fun h => hJ2Q (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨b, hbJ, hbQ⟩ := IsConcreteLE.not_le_iff_exists.mp hJ2eQ
  obtain ⟨J1, hJ1⟩ : Q ^ e ∣ Ideal.span {algebraMap R A π} := Ideal.dvd_iff_le.mpr hle
  have hmem : b * algebraMap R A π ∈ Ideal.span {ϖ ^ e} := by
    have h1 : b * algebraMap R A π ∈ J2 ^ e * Ideal.span {algebraMap R A π} :=
      Ideal.mul_mem_mul hbJ (Ideal.mem_span_singleton_self _)
    have h2 : J2 ^ e * Ideal.span {algebraMap R A π} = Ideal.span {ϖ ^ e} * J1 := by
      rw [hJ1, ← Ideal.span_singleton_pow, hJ2, mul_pow]; ring
    rw [h2] at h1
    exact (Ideal.mul_le_left : Ideal.span {ϖ ^ e} * J1 ≤ Ideal.span {ϖ ^ e}) h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨ϖ, b, a, hϖ0, hbQ, ?_, by rw [← ha, mul_comm]⟩
  intro haQ
  apply hnle
  rw [Ideal.span_singleton_le_iff_mem]
  have h3 : b * algebraMap R A π ∈ Q ^ (e + 1) := by
    rw [← ha, pow_succ']
    exact Ideal.mul_mem_mul haQ (Ideal.pow_mem_pow hϖQ e)
  rcases Ideal.IsPrime.mul_mem_pow Q h3 with h | h
  · exact absurd h hbQ
  · exact h

/-- Residue separability is transitive along a tower of primes. -/
lemma isSeparable_quotient_trans {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (p : Ideal R) (q : Ideal A) (P : Ideal B) [p.IsMaximal] [q.IsMaximal] [P.IsMaximal]
    [q.LiesOver p] [P.LiesOver q] [P.LiesOver p]
    (h1 : Algebra.IsSeparable (R ⧸ p) (A ⧸ q)) (h2 : Algebra.IsSeparable (A ⧸ q) (B ⧸ P)) :
    Algebra.IsSeparable (R ⧸ p) (B ⧸ P) := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  letI : Field (A ⧸ q) := Ideal.Quotient.field _
  letI : Field (B ⧸ P) := Ideal.Quotient.field _
  haveI : IsScalarTower (R ⧸ p) (A ⧸ q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩
    change algebraMap R (B ⧸ P) x = algebraMap (A ⧸ q) (B ⧸ P) (algebraMap R (A ⧸ q) x)
    rw [IsScalarTower.algebraMap_apply R A (B ⧸ P) x,
      IsScalarTower.algebraMap_apply R A (A ⧸ q) x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.algebraMap_mk_of_liesOver]
    rfl
  exact Algebra.IsSeparable.trans _ (A ⧸ q) _

/-- Inertia degree one gives a (trivially) separable residue extension. -/
lemma isSeparable_quotient_of_inertiaDeg_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    (hF : Q.inertiaDeg A = 1) : Algebra.IsSeparable (A ⧸ P) (B ⧸ Q) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field _
  letI : Field (B ⧸ Q) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_eq_of_isMaximal P Q] at hF
  haveI : Module.Free (A ⧸ P) (B ⧸ Q) := Module.Free.of_divisionRing _ _
  have hbot := (Subalgebra.bot_eq_top_iff_finrank_eq_one (F := A ⧸ P) (E := B ⧸ Q)).mpr hF
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra (A ⧸ P) (B ⧸ Q)) := by rw [hbot]; trivial
  obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx
  exact isSeparable_algebraMap y

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
  obtain ⟨ϖ, b, a, hϖ0, hbQ, haQ, hba⟩ := exists_pow_mul_eq R (integralClosure R L) π hπ Q
  rw [← he_def] at hba
  set u : integralClosure R L := b ^ (e - 1) * a with hu_def
  have huQ : u ∉ Q := by
    intro h
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : Q.IsPrime) h with h | h
    · exact hbQ (Ideal.IsPrime.mem_of_pow_mem (inferInstance : Q.IsPrime) _ h)
    · exact haQ h
  -- `w = b t^m / ϖ`, with `wᵉ = u`
  let ϖM : M := algebraMap L M ((ϖ : integralClosure R L) : L)
  let bM : M := algebraMap L M ((b : integralClosure R L) : L)
  let aM : M := algebraMap L M ((a : integralClosure R L) : L)
  have hϖM : ϖM ≠ 0 := by
    simp only [ϖM, ne_eq, map_eq_zero]
    exact fun h => hϖ0 (Subtype.ext h)
  have hbM : bM ≠ 0 := by
    simp only [bM, ne_eq, map_eq_zero]
    intro h
    apply hbQ
    have : b = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have h1 : bM * algebraMap R M π = ϖM ^ e * aM := by
    have := congrArg (fun x : integralClosure R L => algebraMap L M (x : L)) hba
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
    rw [IsScalarTower.algebraMap_apply R L M]
    exact this
  let w : M := bM * t ^ m / ϖM
  have hw : w ^ e = algebraMap L M ((u : integralClosure R L) : L) := by
    rw [hu_def]
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    change (bM * t ^ m / ϖM) ^ e = bM ^ (e - 1) * aM
    rw [div_pow, mul_pow, ← pow_mul, mul_comm m e, ← hm, ht, div_eq_iff (pow_ne_zero _ hϖM)]
    obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    rw [hk] at h1
    linear_combination bM ^ k * h1
  -- `L₁ = L(w)` and `A₂ = integral closure of A₁ in L₁`
  have hwint : IsIntegral L w := ⟨X ^ e - C ((u : integralClosure R L) : L),
    monic_X_pow_sub_C _ he0.ne', by
      rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]⟩
  let L1 : IntermediateField L M := L⟮w⟯
  haveI : FiniteDimensional L L1 := IntermediateField.adjoin.finiteDimensional hwint
  haveI : Algebra.IsSeparable L L1 := Algebra.isSeparable_tower_bot_of_isSeparable L L1 M
  haveI : IsScalarTower (integralClosure R L) L L1 := inferInstance
  haveI : IsDedekindDomain (integralClosure (integralClosure R L) L1) :=
    integralClosure.isDedekindDomain (integralClosure R L) L L1
  haveI : IsFractionRing (integralClosure (integralClosure R L) L1) L1 :=
    integralClosure.isFractionRing_of_finite_extension L L1
  haveI : Module.Finite (integralClosure R L) (integralClosure (integralClosure R L) L1) :=
    IsIntegralClosure.finite (integralClosure R L) L L1 _
  haveI : Module.IsTorsionFree (integralClosure R L) (integralClosure (integralClosure R L) L1) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    have h2 := congrArg (fun x => ((x : L1) : M)) (congrArg Subtype.val hab)
    apply Subtype.ext
    exact (algebraMap L M).injective h2
  -- `w` as an element of `A₂`
  let wL1 : L1 := ⟨w, IntermediateField.mem_adjoin_simple_self L w⟩
  have hwL1 : wL1 ^ e = algebraMap (integralClosure R L) L1 u := by
    apply Subtype.ext
    simp only [wL1, SubmonoidClass.coe_pow]
    exact hw
  have hw2int : IsIntegral (integralClosure R L) wL1 :=
    ⟨X ^ e - C u, monic_X_pow_sub_C _ he0.ne', by
      rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hwL1, sub_self]⟩
  let w2 : integralClosure (integralClosure R L) L1 := ⟨wL1, hw2int⟩
  have hw2 : w2 ^ e = algebraMap (integralClosure R L) _ u := Subtype.ext hwL1
  have hgen : Algebra.adjoin L {algebraMap (integralClosure (integralClosure R L) L1) L1 w2} = ⊤ :=
    algebra_adjoin_gen_eq_top hwint
  -- the map `A₂ → A₃` and the towers
  letI : Algebra R (integralClosure (integralClosure R L) L1) :=
    ((algebraMap (integralClosure R L) (integralClosure (integralClosure R L) L1)).comp
      (algebraMap R (integralClosure R L))).toAlgebra
  haveI : IsScalarTower R (integralClosure R L) (integralClosure (integralClosure R L) L1) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let f23 : integralClosure (integralClosure R L) L1 →+* M :=
    (L1.val.toRingHom).comp ((integralClosure (integralClosure R L) L1).val.toRingHom)
  have hf23 : ∀ x, f23 x ∈ integralClosure R M := by
    intro x
    have h1 : IsIntegral (integralClosure R L) ((x : L1) : M) :=
      x.2.map (L1.val.restrictScalars (integralClosure R L))
    exact isIntegral_trans (R := R) (A := integralClosure R L) _ h1
  let ι23 := f23.codRestrict (integralClosure R M) hf23
  letI : Algebra (integralClosure (integralClosure R L) L1) (integralClosure R M) := ι23.toAlgebra
  haveI : IsScalarTower (integralClosure R L) (integralClosure (integralClosure R L) L1)
      (integralClosure R M) := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI : IsScalarTower R (integralClosure (integralClosure R L) L1) (integralClosure R M) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      apply Subtype.ext
      change algebraMap R M x =
        ((algebraMap R (integralClosure (integralClosure R L) L1) x : L1) : M)
      rw [IsScalarTower.algebraMap_apply R L M x]
      rfl)
  let P : Ideal (integralClosure (integralClosure R L) L1) := Q'.under _
  haveI : P.LiesOver Q := Ideal.LiesOver.tower_bot Q' P Q
  have huP : algebraMap (integralClosure R L) _ u ∉ P := by
    intro h
    apply huQ
    rw [P.over_def Q]
    exact h
  have heA1 : IsUnit ((e : ℕ) : integralClosure R L) := by
    have := heU.map (algebraMap R (integralClosure R L))
    rwa [map_natCast] at this
  have hunr : Algebra.IsUnramifiedAt (integralClosure R L) P :=
    isUnramifiedAt_of_pow_eq (integralClosure R L) L L1 _ e he0 heA1 w2 u hw2 hgen P huP
  -- step (c): `A₂ → A₃`
  haveI : FiniteDimensional L1 M := FiniteDimensional.right L L1 M
  haveI : Algebra.IsSeparable L1 M := Algebra.isSeparable_tower_top_of_isSeparable L L1 M
  haveI : IsScalarTower (integralClosure (integralClosure R L) L1) (integralClosure R M) M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R (integralClosure (integralClosure R L) L1) M :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change algebraMap R M x = _
      rw [IsScalarTower.algebraMap_apply R L M x]
      rfl)
  haveI : Algebra.IsIntegral R (integralClosure (integralClosure R L) L1) :=
    Algebra.IsIntegral.trans (integralClosure R L)
  haveI : IsIntegralClosure (integralClosure R M) (integralClosure (integralClosure R L) L1) M := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · exact ⟨⟨x, isIntegral_trans (R := R) (A := integralClosure (integralClosure R L) L1) x hx⟩,
        rfl⟩
    · rintro ⟨y, rfl⟩
      exact (y.2 : IsIntegral R (y : M)).tower_top
  haveI : Module.Finite (integralClosure (integralClosure R L) L1) (integralClosure R M) :=
    IsIntegralClosure.finite (integralClosure (integralClosure R L) L1) L1 M _
  haveI : Module.IsTorsionFree (integralClosure (integralClosure R L) L1) (integralClosure R M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    have h2 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h2)
  have hm_le : Module.finrank L1 M ≤ m := by
    have hc : w * ϖM / bM ∈ L1 := L1.div_mem (L1.mul_mem (IntermediateField.mem_adjoin_simple_self L w)
      (L1.algebraMap_mem _)) (L1.algebraMap_mem _)
    refine finrank_le_of_pow_eq_field (F := L1) hm0 (t := t) (c := ⟨w * ϖM / bM, hc⟩) ?_ ?_
    · change t ^ m = w * ϖM / bM
      simp only [w]
      field_simp
    · rw [← IntermediateField.restrictScalars_eq_top_iff (K := L),
        IntermediateField.restrictScalars_adjoin_eq_sup, hM, sup_top_eq]
  -- primes and ramification indices
  have hmax0 : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ne,
      Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  haveI : P.LiesOver (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.trans P Q (IsLocalRing.maximalIdeal R)
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hmax0
    rw [(P.over_def (IsLocalRing.maximalIdeal R)), h]
    exact Ideal.comap_bot_of_injective _ (by
      intro a b hab
      apply IsFractionRing.injective R K
      apply (algebraMap K M).injective
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      have h3 : algebraMap L M (algebraMap R L a) = algebraMap L M (algebraMap R L b) :=
        congrArg (fun x => ((x : L1) : M)) (congrArg Subtype.val hab)
      rw [IsScalarTower.algebraMap_apply R L M, IsScalarTower.algebraMap_apply R L M b]
      exact h3)
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  -- `e(Q'|P) · f(Q'|P) ≤ [M : L₁]`
  haveI : IsFractionRing (integralClosure R M) M :=
    integralClosure.isFractionRing_of_finite_extension K M
  have hsum := Ideal.sum_ramification_inertia (integralClosure R M) L1 M hP0
  have hQ'mem : Q' ∈ IsDedekindDomain.primesOverFinset P (integralClosure R M) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hP0 _).mpr ⟨inferInstance, inferInstance⟩
  have hef : P.ramificationIdx' Q' * P.inertiaDeg' Q' ≤ m :=
    le_trans (Finset.single_le_sum (f := fun Q'' => P.ramificationIdx' Q'' * P.inertiaDeg' Q'')
      (fun _ _ => Nat.zero_le _) hQ'mem) (hsum.trans_le hm_le)
  haveI : Q'.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q' P
  rw [Ideal.ramificationIdx'_eq_ramificationIdx P Q' hP0,
    Ideal.inertiaDeg'_eq_inertiaDeg] at hef
  -- `n ∣ e(Q'|𝔪) = e · e(Q'|P)`
  have hdvd := abhyankar_dvd_ramificationIdx (K := K) (L := L) π hπ n hn0 hn t ht hM Q'
  have hPQ : P.ramificationIdx (integralClosure R L) = 1 := Ideal.ramificationIdx_eq_one P _
  have htow1 : Q'.ramificationIdx R =
      P.ramificationIdx R * Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Ideal.ramificationIdx_tower (R := R) P Q'
  have htow2 : P.ramificationIdx R = Q.ramificationIdx R * P.ramificationIdx (integralClosure R L) :=
    Ideal.ramificationIdx_tower (R := R) Q P
  rw [htow2, hPQ, mul_one, ← he_def] at htow1
  have hE0 : 0 < Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Ideal.ramificationIdx_pos _ Q'
  have hF0 : 0 < Q'.inertiaDeg (integralClosure (integralClosure R L) L1) :=
    Ideal.inertiaDeg_pos Q' _
  rw [htow1, hm] at hdvd
  have hmE : m ∣ Q'.ramificationIdx (integralClosure (integralClosure R L) L1) :=
    Nat.dvd_of_mul_dvd_mul_left he0 hdvd
  have hmE' := Nat.le_of_dvd hE0 hmE
  have hE : Q'.ramificationIdx (integralClosure (integralClosure R L) L1) = m := by nlinarith
  have hF : Q'.inertiaDeg (integralClosure (integralClosure R L) L1) = 1 := by nlinarith
  refine ⟨by rw [htow1, hE, hm], ?_⟩
  -- residue fields: `k → κ(Q) → κ(P) → κ(Q')`
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (IsLocalRing.maximalIdeal R)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hmax0
    rw [Q.over_def (IsLocalRing.maximalIdeal R), h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R _)
  haveI : Algebra.IsSeparable (FractionRing (integralClosure R L))
      (FractionRing (integralClosure (integralClosure R L) L1)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (integralClosure R L) L).symm.toRingEquiv
      (FractionRing.algEquiv (integralClosure (integralClosure R L) L1) L1).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (integralClosure R L) L).symm
      (FractionRing.algEquiv (integralClosure (integralClosure R L) L1) L1).symm _
  have hsep12 : Algebra.IsSeparable (integralClosure R L ⧸ Q)
      (integralClosure (integralClosure R L) L1 ⧸ P) := by
    by_contra H
    exact (dvd_differentIdeal_iff.mp
      (dvd_differentIdeal_of_not_isSeparable (integralClosure R L) hQ0 P H)) hunr
  have hsep23 := isSeparable_quotient_of_inertiaDeg_eq_one P Q' hF
  have hsep02 := isSeparable_quotient_trans (IsLocalRing.maximalIdeal R) Q P hsepQ hsep12
  exact isSeparable_quotient_trans (IsLocalRing.maximalIdeal R) P Q' hsep02 hsep23

end Assembly

end TBrauerPurity


namespace PkgI2

universe u

/-! Copied verbatim from `scratch/h-decomposition/Leaves.lean` (section `PkgI2Sec`). -/

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)

end PkgI2

namespace TBrauerPurity

/-- **Leaf T2 (`PkgI2.AbhyankarDVR`), proved.** -/
theorem abhyankarDVR : PkgI2.AbhyankarDVR.{u} := by
  intro R K L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π hπ n hn0 hn htame t ht hM Q _ _
  exact abhyankarDVR_main R K L M π hπ n hn0 hn htame t ht hM Q

end TBrauerPurity

#print axioms TBrauerPurity.abhyankarDVR
