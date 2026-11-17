import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Int
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Split primes in quadratic fields (Mathlib only)

Task bfh-leaf (report `docs/research/bfh-leaf.md`). `SplitsIn K p`: there are two distinct prime
ideals of `𝓞 K` above `p` (Mathlib's `Ideal.primesOver`). For `K` a quadratic number field this is
"`p` splits in `K`". Proved here, from Mathlib's fundamental identity
`Ideal.sum_ramification_inertia_eq_finrank` (`∑ e f = [K : ℚ] = 2`):

* `ef_eq_one`: a prime `P` above a split `p` has `e = f = 1`;
* `exists_int_sub_mem` (`f = 1`): every integer of `K` is congruent to a rational integer mod `P`;
* `natCast_not_mem_sq` (`e = 1`): `p ∉ P²`;
* `zmod_isSquare_of_splitsIn`: if `K` contains `√d`, `p² ∤ d` and `p` splits in `K`, then `d` is a
  nonzero square modulo `p`;
* `mod_eight_of_splitsIn_two`: if `K` contains `√d`, `d` is a fundamental discriminant
  (`Int.IsFundamentalDiscr`, Mathlib) and `2` splits in `K`, then `d ≡ 1 (mod 8)`.
-/

open NumberField

namespace ZInQ.BFHPrinted

/-- `p` splits in `K`: there are two distinct prime ideals of `𝓞 K` above `p`. -/
def SplitsIn (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    ∃ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), P ≠ Q

variable {K : Type*} [Field K] [NumberField K]

theorem ef_eq_one (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime] {P Q : Ideal (𝓞 K)}
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) :
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  set p' : Ideal ℤ := Ideal.span {(p : ℤ)} with hp'
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p' (𝓞 K)
  rw [RingOfIntegers.rank, hK] at hsum
  have hp0 : p' ≠ ⊥ := by
    rw [hp', Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero
  have hpos : ∀ q : p'.primesOver (𝓞 K), 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q
    have h1 : 0 < q.1.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos_of_isDedekindDomain' (p := p') (q := q.1) hp0
    have h2 : 0 < q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos q.1 ℤ
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  have hne : (⟨P, hP⟩ : p'.primesOver (𝓞 K)) ≠ ⟨Q, hQ⟩ := fun h => hPQ (congrArg Subtype.val h)
  have hle := Finset.add_le_sum (f := fun q : p'.primesOver (𝓞 K) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ ⟨P, hP⟩) (Finset.mem_univ ⟨Q, hQ⟩) hne
  have hQ1 := hpos ⟨Q, hQ⟩
  have hP1 := hpos ⟨P, hP⟩
  simp only at hle hQ1 hP1
  have hPe : P.ramificationIdx ℤ * P.inertiaDeg ℤ = 1 := by omega
  exact ⟨Nat.eq_one_of_mul_eq_one_right hPe, Nat.eq_one_of_mul_eq_one_left hPe⟩


theorem span_ne_bot {p : ℕ} [hp : Fact p.Prime] : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero

omit [NumberField K] in
/-- An integer lies in a prime above `p` iff `p` divides it. -/
theorem intCast_mem_iff {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (n : ℤ) :
    (n : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ n := by
  have := hP.2
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (Ideal.span {(p : ℤ)}), Ideal.under,
    Ideal.mem_comap, eq_intCast]

/-- Residue degree one: every integer of `K` is congruent to a rational integer modulo `P`. -/
theorem exists_int_sub_mem (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) (x : 𝓞 K) :
    ∃ n : ℤ, x - (n : 𝓞 K) ∈ P := by
  have hf := (ef_eq_one hK hP hQ hPQ).2
  have := hP.1; have := hP.2
  have : P.IsMaximal :=
    Ideal.IsPrime.isMaximal hP.1 (Ideal.ne_bot_of_liesOver_of_ne_bot (span_ne_bot (p := p)) P)
  let := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  let := Ideal.Quotient.field P
  rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) P] at hf
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 K ⧸ P) one_ne_zero).mp hf
    (Ideal.Quotient.mk P x)
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one,
    Ideal.Quotient.algebraMap_mk_of_liesOver, eq_intCast]

/-- Ramification index one: `p ∉ P²`. -/
theorem natCast_not_mem_sq (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) :
    (p : 𝓞 K) ∉ P ^ 2 := by
  have he := (ef_eq_one hK hP hQ hPQ).1
  have := hP.1; have := hP.2
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (span_ne_bot (p := p))] at he
  intro hmem
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    simpa using hmem
  have hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P ^ n} := by
    by_contra hnb
    have h0 := Nat.sSup_of_not_bddAbove hnb
    rw [Ideal.ramificationIdx', h0] at he
    exact absurd he (by norm_num)
  have h2 := le_csSup hbdd (show 2 ∈ _ from hle)
  rw [Ideal.ramificationIdx'] at he
  omega

omit [NumberField K] in
/-- If `p u ∈ P²` with `p ∤ u` and `p ∈ P`, then `p ∈ P²`. -/
theorem natCast_mem_sq_of_mul {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hpP : (p : 𝓞 K) ∈ P)
    {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (h : ((p : ℤ) * u : 𝓞 K) ∈ P ^ 2) : (p : 𝓞 K) ∈ P ^ 2 := by
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hu
  have e : (p : 𝓞 K) = (b : 𝓞 K) * ((p : ℤ) * u : 𝓞 K) + (a : 𝓞 K) * ((p : 𝓞 K) * (p : 𝓞 K)) := by
    have := congrArg (fun z : ℤ => ((z * p : ℤ) : 𝓞 K)) hab
    simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast] at this
    push_cast
    linear_combination -this
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h)
    (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hpP hpP))

omit [NumberField K] in
/-- An element of `K` satisfying a monic quadratic over `ℤ` is an integer of `K`. -/
theorem exists_ringOfIntegers_of_sq {x : K} {b c : ℤ} (h : x ^ 2 = b * x + c) :
    ∃ y : 𝓞 K, (y : K) = x := by
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.C b * Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      compute_degree!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow, h]
      simp
  exact ⟨⟨x, hint⟩, rfl⟩


omit [NumberField K] in
theorem natCast_mem {p : ℕ} {P : Ideal (𝓞 K)} (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :
    (p : 𝓞 K) ∈ P := by
  have := (intCast_mem_iff hP (p : ℤ)).mpr dvd_rfl
  simpa using this

omit [NumberField K] in
theorem quad_of_coe {r : 𝓞 K} {x : K} (hr : (r : K) = x) {b c : ℤ} (hx : x ^ 2 = b * x + c) :
    r ^ 2 = (b : 𝓞 K) * r + (c : 𝓞 K) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_pow, map_intCast] at hr ⊢
  rw [hr, hx]

omit [NumberField K] in
theorem sq_eq_of_coe {r : 𝓞 K} {x : K} (hr : (r : K) = x) {a : ℤ} (hx : x ^ 2 = a) :
    r ^ 2 = (a : 𝓞 K) := by
  have := quad_of_coe hr (b := 0) (c := a) (by rw [hx]; simp)
  simpa using this

/-- **A prime `p` with `p² ∤ d` that splits in a quadratic field containing `√d` has
`(d / p) = 1`**: `d` is a nonzero square modulo `p`. -/
theorem zmod_isSquare_of_splitsIn (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime]
    (hs : SplitsIn K p) {δ : K} {d : ℤ} (hδ : δ ^ 2 = d) (hd : ¬ (p : ℤ) ^ 2 ∣ d) :
    (d : ZMod p) ≠ 0 ∧ IsSquare (d : ZMod p) := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := hs
  have := hP.1
  obtain ⟨r, hr⟩ := exists_ringOfIntegers_of_sq (b := 0) (c := d) (by rw [hδ]; simp)
  have hr2 : r ^ 2 = (d : 𝓞 K) := sq_eq_of_coe hr hδ
  constructor
  · intro h0
    obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h0
    have hu' : ¬ (p : ℤ) ∣ u := by
      rintro ⟨v, rfl⟩; exact hd ⟨v, by rw [hu]; ring⟩
    have hdP : (d : 𝓞 K) ∈ P := (intCast_mem_iff hP d).mpr ⟨u, hu⟩
    have hrP : r ∈ P := hP.1.mem_of_pow_mem 2 (hr2 ▸ hdP)
    have hr2P : r ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hrP 2
    refine natCast_not_mem_sq hK hP hQ hPQ (natCast_mem_sq_of_mul hp.out (natCast_mem hP) hu' ?_)
    rw [hr2, hu] at hr2P; push_cast at hr2P ⊢; exact hr2P
  · obtain ⟨n, hn⟩ := exists_int_sub_mem hK hP hQ hPQ r
    have hmem : ((n ^ 2 - d : ℤ) : 𝓞 K) ∈ P := by
      have : ((n ^ 2 - d : ℤ) : 𝓞 K) = -((r - n) * (r + n)) := by
        push_cast; linear_combination hr2
      rw [this]; exact P.neg_mem_iff.mpr (P.mul_mem_right _ hn)
    have hdvd := (intCast_mem_iff hP _).mp hmem
    refine ⟨(n : ZMod p), ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at this
    linear_combination -this

omit [NumberField K] in
/-- `2 ∈ P²` from an integer `≡ 2 (mod 4)` in `P²`. -/
theorem two_mem_sq_of {P : Ideal (𝓞 K)} (h2P : (2 : 𝓞 K) ∈ P) {a : ℤ} (ha : a % 4 = 2)
    (haP : (a : 𝓞 K) ∈ P ^ 2) : ((2 : ℕ) : 𝓞 K) ∈ P ^ 2 := by
  refine natCast_mem_sq_of_mul Nat.prime_two (by exact_mod_cast h2P) (u := a / 2) (by omega) ?_
  have e : ((2 : ℕ) : ℤ) * (a / 2) = a := by omega
  rw [← Int.cast_mul, e]; exact haP

/-- **`2` split in a quadratic field containing `√d`, `d` a fundamental discriminant, forces
`d ≡ 1 (mod 8)`.** -/
theorem mod_eight_of_splitsIn_two (hK : Module.finrank ℚ K = 2) (hs : SplitsIn K 2) {δ : K} {d : ℤ}
    (hδ : δ ^ 2 = d) (hd : Int.IsFundamentalDiscr d) : d % 8 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := hs
  have := hP.1
  have h2P : (2 : 𝓞 K) ∈ P := by exact_mod_cast natCast_mem hP
  have hns := natCast_not_mem_sq hK hP hQ hPQ
  have hint : ∀ n : ℤ, (n : 𝓞 K) ∈ P ↔ 2 ∣ n := fun n => by
    simpa using intCast_mem_iff hP n
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hd with ⟨h1, -⟩ | ⟨h0, -, hm⟩
  · -- `ω = (1 + δ)/2` with `ω² = ω + (d − 1)/4`
    set c := d / 4 with hc
    have hdc : d = 4 * c + 1 := by omega
    obtain ⟨w, hw⟩ := exists_ringOfIntegers_of_sq (K := K) (x := (1 + δ) / 2) (b := 1) (c := c) (by
      have : (d : K) = 4 * c + 1 := by rw [hdc]; push_cast; ring
      rw [div_pow, add_sq, hδ, this]; push_cast; ring)
    have hw2 : w ^ 2 = w + (c : 𝓞 K) := by
      have := quad_of_coe hw (b := 1) (c := c) (by
        have : (d : K) = 4 * c + 1 := by rw [hdc]; push_cast; ring
        rw [div_pow, add_sq, hδ, this]; push_cast; ring)
      simpa using this
    obtain ⟨n, hn⟩ := exists_int_sub_mem hK hP hQ hPQ w
    have hnn : ((n * (n - 1) : ℤ) : 𝓞 K) ∈ P := (hint _).mpr (by
      rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (n - 1), by rw [hk]; ring⟩
      · exact ⟨n * k, by rw [hk]; ring⟩)
    have hcP : (c : 𝓞 K) ∈ P := by
      have e : (c : 𝓞 K) = (w - n) * (w + n - 1) + ((n * (n - 1) : ℤ) : 𝓞 K) := by
        push_cast; linear_combination -hw2
      rw [e]; exact P.add_mem (P.mul_mem_right _ hn) hnn
    have := (hint c).mp hcP
    omega
  · -- `s = δ/2` with `s² = m = d/4`, `m ≡ 2, 3 (mod 4)`
    set m := d / 4 with hmdef
    have hdm : d = 4 * m := by omega
    obtain ⟨s, hs⟩ := exists_ringOfIntegers_of_sq (K := K) (x := δ / 2) (b := 0) (c := m) (by
      have : (d : K) = 4 * m := by rw [hdm]; push_cast; ring
      rw [div_pow, hδ, this]; push_cast; ring)
    have hs2 : s ^ 2 = (m : 𝓞 K) := by
      have := quad_of_coe hs (b := 0) (c := m) (by
        have : (d : K) = 4 * m := by rw [hdm]; push_cast; ring
        rw [div_pow, hδ, this]; push_cast; ring)
      simpa using this
    exfalso
    rcases hm with hm2 | hm3
    · have hmP : (m : 𝓞 K) ∈ P := (hint m).mpr (by omega)
      have hsP : s ∈ P := hP.1.mem_of_pow_mem 2 (hs2 ▸ hmP)
      have := Ideal.pow_mem_pow hsP 2
      rw [hs2] at this
      exact hns (two_mem_sq_of h2P hm2 this)
    · obtain ⟨n, hn⟩ := exists_int_sub_mem hK hP hQ hPQ s
      have hn1 : ((n - 1 : ℤ) : 𝓞 K) ∈ P := by
        rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · exfalso
          have hnP : (n : 𝓞 K) ∈ P := (hint n).mpr ⟨k, by rw [hk]; ring⟩
          have hsP : s ∈ P := by simpa using P.add_mem hn hnP
          have hmP : (m : 𝓞 K) ∈ P := hs2 ▸ P.pow_mem_of_mem hsP 2 two_pos
          have := (hint m).mp hmP
          omega
        · exact (hint _).mpr ⟨k, by rw [hk]; ring⟩
      have htP : s - 1 ∈ P := by
        have := P.add_mem hn hn1
        push_cast at this; simpa using this
      have hsq : ((m - 1 : ℤ) : 𝓞 K) ∈ P ^ 2 := by
        have e : ((m - 1 : ℤ) : 𝓞 K) = (s - 1) * (s - 1) + 2 * (s - 1) := by
          push_cast; linear_combination -hs2
        rw [e, pow_two]
        exact (P * P).add_mem (Ideal.mul_mem_mul htP htP) (Ideal.mul_mem_mul h2P htP)
      exact hns (two_mem_sq_of h2P (by omega) hsq)

end ZInQ.BFHPrinted
