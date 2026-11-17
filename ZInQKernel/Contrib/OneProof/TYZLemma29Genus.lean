import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.TYZChain.Thm35
import ZInQKernel.Contrib.TYZGenus.RingClass

/-!
# TYZ Lemma 2.9 (`hL29`) from TYZ Theorem 2.1 for every pair and TYZ Lemma 2.8, through genus theory

Task h29-proof (2026-11-16); report `docs/research/h29-proof.md`, log and computations in
`scratch/h29-proof/`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Asian J. Math. 21 (2017). The source `Period7.tex` was **not on the host** for this task: every line number
`Lnnnn` below is quoted from the project notes that read it (`h29-split.md`, `h29-fix.md`, `h29-ne3.md`,
`rv-tyz-inputs.md`), not re-read here.

**What this file proves.** The top hypothesis `hL29 = H29Split.TYZLemma29PrintedNe3` (TYZ Lemma 2.9 as
printed, squarefree `1 < n ≡ 1, 3 (mod 8)`, `n ≠ 3`) follows from two printed statements of TYZ §2
(`tyzLemma29PrintedNe3_of_genus`):

* `TYZThm21Pairs`: TYZ Theorem 2.1 (L554–559) for every decomposition `n = d₁d₂`: the quadratic period
  `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552) vanishes if neither `d₁` nor `d₂` is `≡ 1 (mod 8)`,
  and equals `±2^{k−1} w_K 𝓛(d₁)𝓛(d₂)` if `d₂ ≡ 1 (mod 8)` (`k` the number of primes of `n`, `a = 1`);
* `TYZLemma28Sym`: TYZ Lemma 2.8 (L1009–1057), `P(d₁, d₂) = P(d₂, d₁)` for `n ≡ 1 (mod 8)`.

The glue is TYZ's own proof of Lemma 2.9 (L1068–1077 with (PQ), L1001): the genus characters `χ_T`,
`T ⊆ {primes of n}`, satisfy `Σ_T χ_T(t) = 2^k [t ∈ Cl²]` (Gauss's principal genus theorem, proved in the
project: `RouteK.Redei.range_sq_eq_ker_chi`), so `Σ_{d₂ ∣ n} P(n/d₂, d₂) = 2^k Q(n)`; for `n ≡ 3 (mod 8)`,
`χ_T = χ_{T^c}` (the product formula, `TYZ35.prod_sgn_chi_eq_one`) pairs `d₂ ≡ 3` with `d₁ ≡ 1`; for
`n ≡ 1 (mod 8)` Lemma 2.8 pairs `(d₁, d₂)` with `(d₂, d₁)`; and `w_K = #μ(K)/2 = 1` for `n ≠ 3`
(`torsionOrder_qNeg_eq_two`).

The same two leaves give the `w_K` form `TYZLemma29Printed` for every `n` including `3`
(`tyzLemma29Printed_of_genus`) and the instance `TYZThm21At31` (`tyzThm21At31_of_thm21Pairs`), and so
`h29 = TYZLemma29Mod2` from five leaves (`tyzLemma29Mod2_of_genusLeaves`).

**Rating (fallback).** This replaces one printed leaf (`hL29`) by two printed leaves; it does not lower the
count. It is the reduction of TYZ Lemma 2.9 to the theorem TYZ derive it from (Theorem 2.1, itself from the
explicit Waldspurger formula, TYZ Theorem 4.2) plus Lemma 2.8. An outright proof of `hL29` needs the explicit
Waldspurger formula, which is not in Lean (see the report).

**`χ_{d₁,d₂}`.** The leaves use the project's genus characters
`TYZ35.gchar n T = Π_{q ∈ T} χ_q`, `χ_q([𝔞]) = (N𝔞/q)` (`RouteK.Redei.chi`), with `T` the primes of `d₂`
(`TYZ35.divSet n d₂`). By Jacobi reciprocity `χ_T` is the character of `K_n(√d₂*)/K_n`,
`d* = (−1)^{(d−1)/2} d` (STANDARD); TYZ's convention `χ_{n,1} = 1` (L510) and `χ_{d₁,d₂} = χ_{d₂,d₁}` for `n ≡ 3` (L994–995) fit this, as does
`χ_{d₁,d₂} = χ_{d₂,d₁}χ₀` for `n ≡ 1` (derived in `rv-tyz-inputs.md` §1.2 from `d₁*d₂* = n`). The two leaves
are insensitive to the choice between `χ_{T(d₂)}` and `χ_{T(d₁)}`: for `n ≡ 3` the two characters agree
(product formula), and for `n ≡ 1` both clauses of `TYZThm21Pairs` and `TYZLemma28Sym` are invariant under
`d₁ ↔ d₂`, since `d₂ ≡ 1 ⇔ d₁ ≡ 1 (mod 8)`. (Independent model review, h29-proof log step 5.)

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Genus

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b NumberField
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet sgn2 sgnHom sum_finset_eq_sum_divisors divSet_div
  prod_sgn_chi_eq_one)
open scoped Quaternion

/-! ## §1. TYZ's quadratic periods and the two leaves -/

/-- **TYZ's quadratic period** `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552), for the embedding
`τ` and the test vector `f`, indexed by `d₂` (`d₁ = n/d₂`): `χ_{d₁,d₂} = χ_T`, `T` the primes of `d₂`
(`TYZ35.divSet n d₂`), `χ_T = Π_{q ∈ T} χ_q` the genus character (`TYZ35.gchar`; `χ_∅ = 1`). The class
`t` is read in `B̂^×` as `τ̂` of a finite idele in the class (`clLift`; any idele in the class gives the same
value, `H29Split.tv_eq_of_toClassGroup_eq`). -/
def quadPeriod (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (d₂ : ℕ) : ℤ :=
  ∑ t : ClassGroup (𝓞 (QNeg n)),
    gchar n (divSet n d₂) t * f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])

/-- **TYZ Theorem 2.1 (L554–559) for every decomposition, odd classes.** For squarefree `1 < n ≡ 1, 3 (mod 8)`,
every admissible `τ` (L527–534), every test vector `f_n` (L550), every sign choice `ℓ` of `𝓛` (TYZ L336–353;
`ℓ(m)² = 𝓛(m)²`, `IsLcalSign`) and every `n = d₁d₂`:

* if neither `d₁` nor `d₂` is `≡ 1 (mod 8)`, then `P(d₁, d₂) = 0`;
* if `d₂ ≡ 1 (mod 8)`, then `P(d₁, d₂) = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)` with `k` the number of prime factors of
  `n`, `a = 1` (`n` odd) and `2w_K` the number of roots of unity of `K_n` (L557–558; Mathlib's
  `NumberField.Units.torsionOrder`).

Against the print. The print's first assertion is "`P(d₁, d₂) ≠ 0` only if `d₂ ≡ 1 (mod 8)`"; read for
ordered pairs it is false at `n ≡ 3 (mod 8)`, `(d₁, d₂) ≡ (1, 3)` (`P(d₁, d₂) = P(d₂, d₁)`; h29-split §2,
rv-tyz-inputs §1.2 item 4). The leaf states only its consequence for pairs with **no** factor `≡ 1`, which is
what every reading gives and what TYZ's proof of Lemma 2.9 uses. The second clause is the displayed formula with
the factor `w_K` (the h29-fix computation shows Theorem 2.1, not Lemma 2.9, is right at `n = 3`). Restrictions,
each a weakening: odd classes only (TYZ: `n ≡ 1, 2, 3`), `n > 1`. At `n = 3` it contains `TYZThm21At31`
(`tyzThm21At31_of_thm21Pairs`), proved outright by task t21-proof. Checked numerically
(`scratch/h29-proof/genus_check.py`): 14 values of `n` up to 219, 2 embeddings each, every `T`: vanishing and
`P² = 4^{k−1} w_K² 𝓛(d₁)²𝓛(d₂)²` hold. -/
def TYZThm21Pairs : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          quadPeriod n τ f d₂ = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℤ) * (ℓ d₁ * ℓ d₂))

/-- **TYZ Lemma 2.8 (L1009–1057; label `lem2.6`), the symmetry `P(d₁, d₂) = P(d₂, d₁)`**, for squarefree
`1 < n ≡ 1 (mod 8)`, every admissible `τ` (with TYZ's choice `4 ∣ c`, L533, which the proof uses, included in
`AdmissibleTau`) and every test vector `f_n`; stated for the decompositions with `d₂ ≡ 1 (mod 8)` (then also
`d₁ ≡ 1`), the only ones TYZ's proof of Lemma 2.9 uses (a weakening). Here `χ_{d₂,d₁} = χ_{d₁,d₂}χ₀`, so the
lemma is not a formal symmetry. TYZ's proof (as checked in rv-tyz-inputs §1.2 item 3): conjugation by
`g₀ = ai + bj + (c + √n)k`. Checked numerically (`genus_check.py`, the 16 runs with `n ≡ 1 (mod 8)`, every
`T`). -/
def TYZLemma28Sym : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → n % 8 = 1 →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ d₁ d₂ : ℕ, d₁ * d₂ = n → d₂ % 8 = 1 → quadPeriod n τ f d₂ = quadPeriod n τ f d₁

/-! ## §2. Genus theory: the character sum (PQ) -/

section Glue

variable {n : ℕ} [NeZero n]

open Classical in
/-- `Σ_T χ_T(c) = 2^k` if `c ∈ Cl²`, else `0` (Gauss: `Cl² = ⋂_q ker χ_q`, `RouteK.Redei.range_sq_eq_ker_chi`). -/
theorem sum_gchar_cl (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (c : ClassGroup (𝓞 (QNeg n))) :
    ∑ T : Finset n.primeFactors, gchar n T c =
      if c ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range then
        2 ^ n.primeFactors.card else 0 := by
  classical
  have e1 : ∑ T : Finset n.primeFactors, gchar n T c =
      ∏ q : n.primeFactors, (sgn2 (chi n q c) + 1) := by
    rw [Finset.prod_add_one, Finset.powerset_univ]; rfl
  rw [e1]
  have hiff : c ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range ↔
      ∀ q, chi n q c = 1 := by
    rw [range_sq_eq_ker_chi n hn hsq h1, Subgroup.mem_iInf]
    exact forall_congr' fun q => MonoidHom.mem_ker
  split_ifs with hc
  · rw [hiff] at hc
    have : ∀ q : n.primeFactors, sgn2 (chi n q c) + 1 = 2 := fun q => by
      rw [hc q]; simp [sgn2]
    rw [Finset.prod_congr rfl (fun q _ => this q), Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  · rw [hiff, not_forall] at hc
    obtain ⟨q, hq⟩ := hc
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [sgn2, hq]

/-- **(PQ)** (TYZ L1001): `Σ_{d₂ ∣ n} P(n/d₂, d₂) = 2^k Q(n)`. -/
theorem sum_quadPeriod (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (f : ℍ[AQ] → ℤ) :
    ∑ e ∈ n.divisors, quadPeriod n τ f e = 2 ^ n.primeFactors.card * genusPeriodTV n τ f := by
  classical
  have h := sum_finset_eq_sum_divisors (n := n) hsq (fun T => ∑ t : ClassGroup (𝓞 (QNeg n)),
    gchar n T t * f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ]))
  simp only [quadPeriod]
  rw [← h, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_gchar_cl hn hsq h1, ite_mul, zero_mul]
  rw [← Finset.sum_filter, genusPeriodTV, Finset.mul_sum, sqClasses]

/-- For `n ≡ 3 (mod 4)`, `P(d₁, d₂) = P(d₂, d₁)`: `χ_T = χ_{T^c}` (product formula). -/
theorem quadPeriod_div (h4 : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (f : ℍ[AQ] → ℤ) {e : ℕ} (he : e ∣ n) : quadPeriod n τ f (n / e) = quadPeriod n τ f e := by
  classical
  unfold quadPeriod
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hp := prod_sgn_chi_eq_one h4 hsq h1 c
  rw [← Finset.prod_mul_prod_compl (divSet n e)] at hp
  rw [divSet_div hsq he]
  unfold gchar
  change ∏ q ∈ (divSet n e)ᶜ, sgnHom (chi n q c) = ∏ q ∈ divSet n e, sgnHom (chi n q c)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hp with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    rw [h1', h2']

end Glue

/-! ## §3. `w_K = 1` for `n ≠ 3`: the units of `ℚ(√−n)` -/

section Units

theorem eq_three_of_sq_eq_three_mul {d k : ℤ} (hsq : Squarefree d) (h : k ^ 2 = 3 * d) : d = 3 := by
  have h3 : (3 : ℤ) ∣ k := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨d, h⟩
  obtain ⟨j, rfl⟩ := h3
  have hd : d = 3 * j ^ 2 := by linarith [h, show (3 * j) ^ 2 = 9 * j ^ 2 by ring]
  have hj : IsUnit j := hsq j ⟨3, by rw [hd]; ring⟩
  rcases Int.isUnit_iff.mp hj with rfl | rfl <;> simpa using hd

theorem eq_one_of_sq_eq_four_mul {d k : ℤ} (hsq : Squarefree d) (h : k ^ 2 = 4 * d) : d = 1 := by
  have h2 : (2 : ℤ) ∣ k := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨2 * d, by rw [h]; ring⟩
  obtain ⟨j, rfl⟩ := h2
  have hd : d = j ^ 2 := by linarith [h, show (2 * j) ^ 2 = 4 * j ^ 2 by ring]
  have hj : IsUnit j := hsq j ⟨1, by rw [hd]; ring⟩
  rcases Int.isUnit_iff.mp hj with rfl | rfl <;> simpa using hd

open ZInQ.Contrib.TYZGenus.RingClass (exists_two_re normZ_eq_re_im normZ_unit coe_sqrtNeg) in
/-- For squarefree `d > 1`, `d ≠ 3`, the units of `𝓞_{ℚ(√−d)}` are `±1` (adapted from
`TYZGenus.RingClass.unit_eq`, the case `d ≡ 5 (mod 8)`). -/
theorem unit_eq_one_or_neg_one {d : ℕ} [NeZero d] (hsq : Squarefree d) (h1 : 1 < d) (h3 : d ≠ 3)
    (u : (𝓞 (QNeg d))ˣ) : (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
  obtain ⟨m, hm⟩ := exists_two_re (u : 𝓞 (QNeg d))
  obtain ⟨k, hk⟩ := exists_two_re ((u : 𝓞 (QNeg d)) * ZInQ.Contrib.TYZGenus.RingClass.sqrtNeg d)
  have hN := normZ_eq_re_im (u : 𝓞 (QNeg d))
  rw [normZ_unit] at hN
  set x := ((u : 𝓞 (QNeg d)) : QNeg d).re
  set y := ((u : 𝓞 (QNeg d)) : QNeg d).im
  have hre : (((u : 𝓞 (QNeg d)) * ZInQ.Contrib.TYZGenus.RingClass.sqrtNeg d : 𝓞 (QNeg d)) :
      QNeg d).re = -(d : ℚ) * y := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg, y]
  rw [hre] at hk
  have hZ : (d : ℤ) * m ^ 2 + k ^ 2 = 4 * d := by
    have : (d : ℚ) * (m : ℚ) ^ 2 + (k : ℚ) ^ 2 = 4 * d := by
      rw [← hm, ← hk]; linear_combination (4 * (d : ℚ)) * hN.symm
    exact_mod_cast this
  have hd0 : (1 : ℤ) < d := by exact_mod_cast h1
  have hm2 : m ^ 2 ≤ 4 := by
    by_contra h; push Not at h; nlinarith [sq_nonneg k]
  have hmlo : -2 ≤ m := by nlinarith [sq_nonneg (m + 2)]
  have hmhi : m ≤ 2 := by nlinarith [sq_nonneg (m - 2)]
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsq
  have hd3 : (d : ℤ) ≠ 3 := by exact_mod_cast h3
  have hu : ∀ e : ℚ, (e = 1 ∨ e = -1) → x = e → y = 0 →
      (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
    rintro e (rfl | rfl) hx hy
    · left; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
    · right; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
  have hk0 : ∀ mm : ℤ, (mm = 2 ∨ mm = -2) → m = mm → k = 0 := by
    rintro mm (rfl | rfl) rfl <;> nlinarith [sq_nonneg k]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rcases (show m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h | h | h
  · have hkz := hk0 _ (Or.inr rfl) h
    refine hu (-1) (Or.inr rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq
  · exact absurd (eq_three_of_sq_eq_three_mul hsqZ (k := k) (by subst h; linarith)) hd3
  · have := eq_one_of_sq_eq_four_mul hsqZ (k := k) (by subst h; linarith)
    omega
  · exact absurd (eq_three_of_sq_eq_three_mul hsqZ (k := k) (by subst h; linarith)) hd3
  · have hkz := hk0 _ (Or.inl rfl) h
    refine hu 1 (Or.inl rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq

/-- **`#μ(ℚ(√−n)) = 2`** for squarefree `n > 1`, `n ≠ 3`, so TYZ's `w_K` is `1` there. -/
theorem torsionOrder_qNeg_eq_two {n : ℕ} [NeZero n] (hsq : Squarefree n) (h1 : 1 < n) (h3 : n ≠ 3) :
    NumberField.Units.torsionOrder (QNeg n) = 2 := by
  classical
  let := Fintype.ofFinite (NumberField.Units.torsion (QNeg n))
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  rcases unit_eq_one_or_neg_one hsq h1 h3 (x : (𝓞 (QNeg n))ˣ) with h | h
  · left; exact Units.ext h
  · right; exact Units.ext h

end Units

/-! ## §4. Divisor sums -/

section Divisors

theorem mod8_eq_of_dvd {n e : ℕ} (he : e ∣ n) (h : (n / e) % 8 = 1) : e % 8 = n % 8 := by
  obtain ⟨m, rfl⟩ := he
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · simp at h
  · rw [Nat.mul_div_cancel_left _ he0] at h
    rw [Nat.mul_mod, h, mul_one, Nat.mod_mod]

theorem mod8_iff_of_dvd {n e : ℕ} (hn : n % 8 = 1 ∨ n % 8 = 3) (he : e ∣ n) :
    (n / e) % 8 = 1 ↔ e % 8 = n % 8 := by
  obtain ⟨m, rfl⟩ := he
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hn
    · exact h
  rw [Nat.mul_div_cancel_left _ he0]
  rw [Nat.mul_mod] at hn ⊢
  have ha := Nat.mod_lt e (by norm_num : 8 > 0)
  have hb := Nat.mod_lt m (by norm_num : 8 > 0)
  generalize e % 8 = a at *
  generalize m % 8 = b at *
  interval_cases a <;> interval_cases b <;> simp_all

theorem mul_self_ne_of_squarefree {n e : ℕ} (hsq : Squarefree n) (h1 : 1 < n) : e * e ≠ n := by
  intro h
  have := Nat.isUnit_iff.mp (hsq e ⟨1, by rw [mul_one, h]⟩)
  subst this; omega

theorem lt_mul_div_iff {n e : ℕ} (he : e ∣ n) (hn : 0 < n) : n < (n / e) * (n / e) ↔ e * e < n := by
  obtain ⟨m, rfl⟩ := he
  have he0 : 0 < e := Nat.pos_of_mul_pos_right hn
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left _ he0]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : m ≤ e := by nlinarith
    nlinarith
  · intro h
    have : e < m := by nlinarith
    nlinarith

/-- The pairing for `n ≡ 3 (mod 8)`: `d₂ ≡ 3` with `d₁ ≡ 1`; the others vanish. -/
theorem sum_divisors_three {n : ℕ} (hn : n % 8 = 3) (P : ℕ → ℤ)
    (hV : ∀ e ∈ n.divisors, (n / e) % 8 ≠ 1 → e % 8 ≠ 1 → P e = 0)
    (hS : ∀ e ∈ n.divisors, P (n / e) = P e) :
    ∑ e ∈ n.divisors, P e = 2 * ∑ e ∈ pairIdx n, P e := by
  classical
  have hA : ∀ e ∈ n.divisors,
      P e = (if e % 8 = 1 then P e else 0) + (if e % 8 = 3 then P e else 0) := by
    intro e he
    have hiff := mod8_iff_of_dvd (Or.inr hn) (Nat.dvd_of_mem_divisors he)
    by_cases h1 : e % 8 = 1
    · simp [h1]
    · by_cases h3 : e % 8 = 3
      · simp [h3]
      · rw [if_neg h1, if_neg h3, hV e he (fun h => h3 (hn ▸ hiff.1 h)) h1]; simp
  have hB : ∑ e ∈ n.divisors, (if e % 8 = 3 then P e else 0) =
      ∑ e ∈ n.divisors, (if e % 8 = 1 then P e else 0) := by
    rw [← Nat.sum_div_divisors n (fun e => if e % 8 = 1 then P e else 0)]
    refine Finset.sum_congr rfl fun e he => ?_
    have hiff := mod8_iff_of_dvd (Or.inr hn) (Nat.dvd_of_mem_divisors he)
    rw [hn] at hiff
    simp only [hiff, hS e he]
  rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib, hB, ← two_mul, pairIdx, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [hn]

/-- The pairing for `n ≡ 1 (mod 8)`: `(d₁, d₂)` with `(d₂, d₁)`, both `≡ 1`; the others vanish. -/
theorem sum_divisors_one {n : ℕ} (hn : n % 8 = 1) (hsq : Squarefree n) (h1 : 1 < n) (P : ℕ → ℤ)
    (hV : ∀ e ∈ n.divisors, (n / e) % 8 ≠ 1 → e % 8 ≠ 1 → P e = 0)
    (hS : ∀ e ∈ n.divisors, e % 8 = 1 → P (n / e) = P e) :
    ∑ e ∈ n.divisors, P e = 2 * ∑ e ∈ pairIdx n, P e := by
  classical
  have hA : ∀ e ∈ n.divisors, P e = (if e % 8 = 1 ∧ e * e < n then P e else 0) +
      (if e % 8 = 1 ∧ n < e * e then P e else 0) := by
    intro e he
    have hiff := mod8_iff_of_dvd (Or.inl hn) (Nat.dvd_of_mem_divisors he)
    by_cases h8 : e % 8 = 1
    · rcases lt_or_gt_of_ne (mul_self_ne_of_squarefree (e := e) hsq h1) with h | h
      · rw [if_pos ⟨h8, h⟩, if_neg (fun h' => absurd h'.2 (by omega))]; simp
      · rw [if_neg (fun h' => absurd h'.2 (by omega)), if_pos ⟨h8, h⟩]; simp
    · rw [if_neg (fun h' => h8 h'.1), if_neg (fun h' => h8 h'.1),
        hV e he (fun h => h8 (hn ▸ hiff.1 h)) h8]; simp
  have hB : ∑ e ∈ n.divisors, (if e % 8 = 1 ∧ n < e * e then P e else 0) =
      ∑ e ∈ n.divisors, (if e % 8 = 1 ∧ e * e < n then P e else 0) := by
    rw [← Nat.sum_div_divisors n (fun e => if e % 8 = 1 ∧ n < e * e then P e else 0)]
    refine Finset.sum_congr rfl fun e he => ?_
    have hiff := mod8_iff_of_dvd (Or.inl hn) (Nat.dvd_of_mem_divisors he)
    rw [hn] at hiff
    have hlt := lt_mul_div_iff (Nat.dvd_of_mem_divisors he) (by omega : 0 < n)
    by_cases h8 : e % 8 = 1
    · simp only [hiff, hlt, h8, true_and, hS e he h8]
    · simp only [hiff, h8, false_and, if_false]
  rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib, hB, ← two_mul, pairIdx, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [hn]

/-- Choosing the signs. -/
theorem sum_formula {n : ℕ} (s : Finset ℕ) (P : ℕ → ℤ) (c : ℤ) (ℓ : ℕ → ℤ)
    (hF : ∀ e ∈ s, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ P e = ε * c * (ℓ (n / e) * ℓ e)) :
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
      ∑ e ∈ s, P e = c * ∑ e ∈ s, ε e * (ℓ (n / e) * ℓ e) := by
  classical
  choose! ε hε hP using hF
  refine ⟨fun d => if d ∈ s then ε d else 1, fun d => ?_, ?_⟩
  · by_cases h : d ∈ s
    · simp only [h, if_true]; exact hε d h
    · simp only [h, if_false]; left; trivial
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [he, if_true]
    rw [hP e he]; ring

end Divisors

/-! ## §5. TYZ Lemma 2.9 from Theorem 2.1 and Lemma 2.8 -/

/-- **TYZ's proof of Lemma 2.9** (L1068–1077), with `w_K = #μ(K)/2`: from Theorem 2.1 for every pair and
Lemma 2.8, `w_K Σ_{n = d₁d₂, d₂ ≡ 1} ε 𝓛(d₁)𝓛(d₂) = Q(n)`. -/
theorem lemma29_core (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (h1 : 1 < n) (hcl : n % 8 = 1 ∨ n % 8 = 3) {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]}
    (hτ : AdmissibleTau n τ) {f : ℍ[AQ] → ℤ} (hf : IsTestVector n τ f) {ℓ : ℕ → ℤ}
    (hℓ : IsLcalSign ℓ) :
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
      ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℤ) *
        ∑ d ∈ pairIdx n, ε d * (ℓ (n / d) * ℓ d) = genusPeriodTV n τ f := by
  set k := n.primeFactors.card with hkdef
  set w : ℤ := ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℤ) with hwdef
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  have hk : 1 ≤ k := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h1)
  have hdm : ∀ e ∈ n.divisors, n / e * e = n := fun e he =>
    Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he)
  have hV : ∀ e ∈ n.divisors, (n / e) % 8 ≠ 1 → e % 8 ≠ 1 → quadPeriod n τ f e = 0 := fun e he h h' =>
    (h21 n hsq h1 hcl τ hτ f hf ℓ hℓ (n / e) e (hdm e he)).1 h h'
  have hsum : ∑ e ∈ n.divisors, quadPeriod n τ f e = 2 * ∑ e ∈ pairIdx n, quadPeriod n τ f e := by
    rcases hcl with h | h
    · exact sum_divisors_one h hsq h1 (quadPeriod n τ f) hV fun e he he1 =>
        (h28 n hsq h1 h τ hτ f hf (n / e) e (hdm e he) he1).symm
    · exact sum_divisors_three h (quadPeriod n τ f) hV fun e he =>
        quadPeriod_div (by omega) hsq h1 τ f (Nat.dvd_of_mem_divisors he)
  have hF : ∀ e ∈ pairIdx n, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      quadPeriod n τ f e = ε * (2 ^ (k - 1) * w) * (ℓ (n / e) * ℓ e) := by
    intro e he
    have hmem := Finset.mem_filter.mp he
    obtain ⟨ε, hε, heq⟩ :=
      (h21 n hsq h1 hcl τ hτ f hf ℓ hℓ (n / e) e (hdm e hmem.1)).2 hmem.2.1
    exact ⟨ε, hε, by rw [heq]; ring⟩
  obtain ⟨ε, hε, hP⟩ := sum_formula (n := n) _ (quadPeriod n τ f) _ ℓ hF
  refine ⟨ε, hε, ?_⟩
  have hPQ := sum_quadPeriod hn hsq h1 τ f
  rw [hsum, hP] at hPQ
  have h2k : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2k] at hPQ
  have hne : (2 : ℤ) * 2 ^ (k - 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination hPQ

/-- **`hL29` (TYZ Lemma 2.9 as printed, `n ≠ 3`) from TYZ Theorem 2.1 for every pair and TYZ Lemma 2.8.** -/
theorem tyzLemma29PrintedNe3_of_genus (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym) :
    TYZLemma29PrintedNe3 := by
  intro n _ hsq h1 h3 hcl τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, h⟩ := lemma29_core h21 h28 hsq h1 hcl hτ hf hℓ
  refine ⟨ε, hε, ?_⟩
  rw [torsionOrder_qNeg_eq_two hsq h1 h3] at h
  norm_num at h
  exact h

/-- The `w_K` form of TYZ Lemma 2.9 (`H29Split.TYZLemma29Printed`, every `n` including `3`) from the same two
leaves. -/
theorem tyzLemma29Printed_of_genus (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym) :
    TYZLemma29Printed := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, h⟩ := lemma29_core h21 h28 hsq h1 hcl hτ hf hℓ
  refine ⟨ε, hε, ?_⟩
  by_cases h3 : n = 3
  · subst h3
    rw [wK_three_eq_torsionOrder]
    exact h
  · rw [torsionOrder_qNeg_eq_two hsq h1 h3] at h
    rw [show wK n = 1 by simp [wK, h3]]
    norm_num at h ⊢
    exact h

/-- `TYZThm21Pairs` contains `H29Split.TYZThm21At31` (its instance `n = 3`, `(d₁, d₂) = (3, 1)`). -/
theorem tyzThm21At31_of_thm21Pairs (h21 : TYZThm21Pairs) : TYZThm21At31 := by
  intro τ hτ f hf ℓ hℓ
  have hsq3 : Squarefree 3 := Nat.prime_three.prime.squarefree
  obtain ⟨ε, hε, heq⟩ :=
    (h21 3 hsq3 (by norm_num) (Or.inr rfl) τ hτ f hf ℓ hℓ 3 1 (by norm_num)).2 (by norm_num)
  refine ⟨ε, hε, ?_⟩
  have hd : divSet 3 1 = ∅ := by
    ext q
    simp only [ZInQ.Contrib.TYZGenus.TYZ35.divSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, Nat.dvd_one]
    exact (Nat.prime_of_mem_primeFactors q.2).one_lt.ne'
  have hk : (Nat.primeFactors 3).card = 1 := by
    rw [Nat.Prime.primeFactors Nat.prime_three, Finset.card_singleton]
  unfold quadPeriod at heq
  simp only [hd, gchar, Finset.prod_empty, one_mul, hk] at heq
  rw [heq]
  norm_num

/-- **`h29 = TYZLemma29Mod2` from five printed statements**: Legendre, Jones–Pall, TYZ's test vector,
TYZ Theorem 2.1 for every pair, TYZ Lemma 2.8, TYZ Proposition 2.3. -/
theorem tyzLemma29Mod2_of_genusLeaves (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym)
    (h23 : TYZProp23Printed) : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_printedLeaves_legendre hL hJ hfx (tyzLemma29Printed_of_genus h21 h28) h23

end ZInQ.Contrib.TYZDecomp.H29Genus
