import Mathlib

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

end TBrauerPurity

#print axioms TBrauerPurity.abhyankar_dvd_ramificationIdx
#print axioms TBrauerPurity.ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq
#print axioms TBrauerPurity.abhyankarDVR_conclusion_of_L_eq_K
