import ZInQKernel.Contrib.OneProof.RC.Stages.LocalTorsionBound
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree
import Mathlib.FieldTheory.Finite.GaloisField

/-! The residue counts in the degree-four torsion bound (tex 8274–8285). -/

noncomputable section

open scoped NumberField WeierstrassCurve
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve TauCeti

namespace ZInQ.Manuscript.RC.Stages

/-- The point count on an integral equation over the field of order p^f. -/
def finiteCount (C : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (f : ℕ) : ℕ :=
  Nat.card (C.map (Int.castRingHom (GaloisField p f))).toAffine.Point

theorem finiteCount_pos (C : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (f : ℕ) :
    0 < finiteCount C p f := by
  let W := (C.map (Int.castRingHom (GaloisField p f))).toAffine
  let T := {xy : GaloisField p f × GaloisField p f // W.Nonsingular xy.1 xy.2}
  letI : Finite T := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (WithZero T) := inferInstanceAs (Finite (Option T))
  letI : Finite W.Point := Finite.of_equiv _ W.nonsingularPointEquiv.symm
  letI : Nonempty W.Point := ⟨.zero⟩
  exact Nat.card_pos

/-- An integral nonsingular equation admits two distinct primes of good reduction. -/
theorem exists_two_good_primes (C : WeierstrassCurve ℤ) (hC : C.Δ ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ ¬ (p : ℤ) ∣ C.Δ ∧ ¬ (q : ℤ) ∣ C.Δ := by
  obtain ⟨p, hpC, hp⟩ := Nat.exists_infinite_primes (C.Δ.natAbs + 1)
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hav {r : ℕ} (hr : C.Δ.natAbs < r) (h : (r : ℤ) ∣ C.Δ) : False :=
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hC) hr)
      (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h)
  exact ⟨p, q, hp, hq, by omega, hav (by omega), hav (by omega)⟩

/-- Isomorphic finite fields give the same point count on the same integral equation. -/
private theorem pointCount_eq {k l : Type*} [Field k] [Field l] (e : k ≃+* l)
    (C : WeierstrassCurve ℤ) :
    Nat.card (C.map (Int.castRingHom k)).toAffine.Point =
      Nat.card (C.map (Int.castRingHom l)).toAffine.Point := by
  let Wk := (C.map (Int.castRingHom k)).toAffine
  let Wl := (C.map (Int.castRingHom l)).toAffine
  have hmap : Wk.map e.toRingHom = Wl := by
    change (C.map (Int.castRingHom k)).map e.toRingHom = _
    rw [WeierstrassCurve.map_map]
    congr 1
    ext n
    exact map_intCast e n
  have hxy (x y : k) : Wl.Nonsingular (e x) (e y) ↔ Wk.Nonsingular x y := by
    rw [← hmap]
    exact Wk.map_nonsingular (f := e.toRingHom) e.injective x y
  apply Nat.card_congr
  refine Wk.nonsingularPointEquiv.trans ((Equiv.optionCongr ?_).trans Wl.nonsingularPointEquiv.symm)
  exact (Equiv.prodCongr e.toEquiv e.toEquiv).subtypeEquiv (fun z => (hxy z.1 z.2).symm)

open IsDedekindDomain.HeightOneSpectrum in
/-- The residue field bound uses the actual residue field of the valuation
subring and identifies its point count with the canonical finite-field count. -/
theorem numberField_product_kills (C : WeierstrassCurve ℤ) {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K ≤ 4) (u : HeightOneSpectrum (𝓞 K))
    [Algebra (𝓞 K) (u.valuation K).valuationSubring]
    [IsScalarTower (𝓞 K) (u.valuation K).valuationSubring K]
    {p : ℕ} [Fact p.Prime] (hp : rationalPrimeBelow u = p) (hgood : ¬ (p : ℤ) ∣ C.Δ)
    {n : ℕ} (hn : ¬ p ∣ n)
    (P : (C.map (Int.castRingHom K)).toAffine.Point) (hP : n • P = 0) :
    reductionBound (finiteCount C p) • P = 0 := by
  classical
  let R := (u.valuation K).valuationSubring
  let k := ResidueField R
  let W := (C.map (Int.castRingHom K)).toAffine
  let f := u.asIdeal.inertiaDeg ℤ
  have hf₁ : 1 ≤ f := Ideal.inertiaDeg_pos u.asIdeal ℤ
  have hf₄ : f ≤ 4 := by
    have he := u.absNorm_dvd_rationalPrimeBelow_pow_finrank
    rw [absNorm_eq_rationalPrimeBelow_pow, hp] at he
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      (Nat.le_of_dvd (Nat.pow_pos (Fact.out : p.Prime).pos) he) |>.trans hK
  have hk : Nat.card k = p ^ f := by
    change Nat.card (R ⧸ maximalIdeal R) = _
    rw [← Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal u.asIdeal R).toEquiv]
    change Ideal.absNorm u.asIdeal = p ^ f
    rw [absNorm_eq_rationalPrimeBelow_pow, hp]
  have hnot (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) : (m : 𝓞 K) ∉ u.asIdeal := by
    rw [intCast_mem_asIdeal_iff, hp]
    exact hm
  have hnotn : (n : 𝓞 K) ∉ u.asIdeal := by
    simpa only [Int.cast_natCast] using hnot (n : ℤ) (by exact_mod_cast hn)
  let C₀ := C.map (Int.castRingHom R)
  have hbase : C₀⁄K = W := by
    change (C.map (Int.castRingHom R)).map (algebraMap R K) = _
    rw [WeierstrassCurve.map_map]
    congr 1
  haveI : WeierstrassCurve.IsIntegral R W := ⟨C₀, hbase.symm⟩
  have hmodel : integralModel R W = C₀ := integralModel_eq_of_baseChange_eq hbase
  have hu : IsUnit C₀.Δ := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    simp only [C₀, map_Δ]
    change (C.Δ : R) ∉ _
    rw [← map_intCast (algebraMap (𝓞 K) R),
      algebraMap_mem_maximalIdeal_valuationSubring_iff (K := K) u]
    exact hnot _ hgood
  haveI : (integralModel R W).IsElliptic := ⟨hmodel.symm ▸ hu⟩
  letI := Fintype.ofFinite (GaloisField p f)
  letI := Fintype.ofFinite k
  let e : GaloisField p f ≃+* k := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card _ _ (by omega), hk])
  have hcount : finiteCount C p f =
      Nat.card ((integralModel R W).map (residue R)).toAffine.Point := by
    rw [hmodel]
    unfold C₀
    rw [WeierstrassCurve.map_map]
    have hh : (residue R).comp (Int.castRingHom R) = Int.castRingHom k := by
      ext m
      exact map_intCast (residue R) m
    rw [hh]
    exact pointCount_eq e C
  exact reduction_product_kills u (finiteCount C p) hf₁ hf₄ hcount hnotn hP

/-- Every number field has a height-one prime above p, and its valuation
ring contains the ring of integers. -/
theorem numberField_prime_product_kills (C : WeierstrassCurve ℤ) {K : Type*}
    [Field K] [NumberField K] [DecidableEq K] (hK : Module.finrank ℚ K ≤ 4)
    {p : ℕ} [Fact p.Prime] (hgood : ¬ (p : ℤ) ∣ C.Δ) {n : ℕ} (hn : ¬ p ∣ n)
    (P : (C.map (Int.castRingHom K)).toAffine.Point) (hP : n • P = 0) :
    reductionBound (finiteCount C p) • P = 0 := by
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI : J.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨u⟩ := (inferInstance : Nonempty (J.primesOver (𝓞 K)))
  have huP : u.val.IsPrime := u.property.1
  have huJ : u.val.under ℤ = J := (Ideal.liesOver_iff _ _).mp u.property.2 |>.symm
  have hu₀ : u.val ≠ ⊥ := by
    intro he
    have hmem : (p : ℤ) ∈ u.val.under ℤ := by rw [huJ]; exact Ideal.subset_span rfl
    rw [he] at hmem
    exact (Fact.out : p.Prime).ne_zero
      (by simpa [Ideal.under] using hmem)
  let v : HeightOneSpectrum (𝓞 K) := ⟨u.val, huP, hu₀⟩
  let R := (v.valuation K).valuationSubring
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R.toSubring
    (fun x => (v.valuation K).mem_valuationSubring_iff _ |>.mpr (v.valuation_le_one (K := K) x))
  letI : Algebra (𝓞 K) R := f.toAlgebra
  letI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply numberField_product_kills C hK v _ hgood hn P hP
  change Ideal.absNorm (u.val.under ℤ) = p
  rw [huJ]
  simp [J, Ideal.absNorm_span_natCast]

/-- The same product of eight point counts kills torsion over every number
field of degree at most four. -/
theorem uniform_two_prime_bound (C : WeierstrassCurve ℤ) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hp : ¬ (p : ℤ) ∣ C.Δ) (hq : ¬ (q : ℤ) ∣ C.Δ)
    {K : Type*} [Field K] [NumberField K] [DecidableEq K] (hK : Module.finrank ℚ K ≤ 4)
    {P : (C.map (Int.castRingHom K)).toAffine.Point} (hP : IsOfFinAddOrder P) :
    (reductionBound (finiteCount C p) * reductionBound (finiteCount C q)) • P = 0 :=
  two_good_prime_bound Fact.out Fact.out hpq
    (fun _ hn P hP => numberField_prime_product_kills C hK hp hn P hP)
    (fun _ hn P hP => numberField_prime_product_kills C hK hq hn P hP) hP

#print axioms pointCount_eq
#print axioms finiteCount_pos
#print axioms exists_two_good_primes
#print axioms numberField_product_kills
#print axioms numberField_prime_product_kills
#print axioms uniform_two_prime_bound

end ZInQ.Manuscript.RC.Stages
