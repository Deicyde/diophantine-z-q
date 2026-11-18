import ZInQKernel.Contrib.CloudB3RC53.Splitting.Core

/-!
# Splitting in a quadratic field, part 2: the splitting criterion

`splittingCriterion_proof : GenusOdd.SplittingCriterion` (stated in
`CloudB3RC53/GenusOdd/Glue.lean`, where it was introduced as a GLUE input of (3.4), tex L2428 "All level primes split",
from the squareclass conditions of tex L2405–2406, L2350–2352, and used for the final companion,
tex L2604–2613): for a quadratic field `K` and a prime `p` at which `D = disc K` is a unit square
(`SquareAt p D`: `p ∤ D` and `D` a square mod `p` for odd `p`, `D ≡ 1 mod 8` for `p = 2`), `p`
splits in `K` (`CST.SplitsIn`). PROVED:

* `exists_sqrt_gen`: `K = ℚ(θ)` with `θ ∈ 𝓞_K`, `θ² = m`, `m` a squarefree integer;
* `minpoly_eq_of_aeval`: a monic quadratic over `ℚ` killing an irrational element of `K` is its
  minimal polynomial;
* `discr_eq_mul_sq`: `disc K = (u² − 4v) q²` with `q ∈ ℚ` for a generator with
  `minpoly = X² + uX + v` (change of basis from `(1, θ)` to an integral basis);
* for odd `p`: `m` is a nonzero square mod `p`, and Kummer–Dedekind applies to `θ`
  (`X² − m ≡ (X − c)(X + c)`); for `p = 2`: `m ≡ 1 mod 8`, and it applies to `(1 + θ)/2`
  (`X² − X − (m − 1)/4 ≡ X(X − 1) mod 2`).
-/

noncomputable section

open Polynomial NumberField

namespace ZInQ.Contrib.CloudB3RC53.Splitting

variable {K : Type} [Field K] [NumberField K]

/-- A monic quadratic over `ℚ` (with integer coefficients) killing an element of `K \ ℚ` is its
minimal polynomial. -/
theorem minpoly_eq_of_aeval (_hK : Module.finrank ℚ K = 2) {x : K}
    (hx : x ∉ (algebraMap ℚ K).range) (u v : ℤ)
    (h : x ^ 2 + (u : K) * x + v = 0) :
    minpoly ℚ x = X ^ 2 + C (u : ℚ) * X + C (v : ℚ) := by
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hmon : (X ^ 2 + C (u : ℚ) * X + C (v : ℚ)).Monic := by monicity!
  have hroot : aeval x (X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) = 0 := by
    simpa using h
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd ℚ x hroot) ?_).symm
  rw [natDegree_quad]
  exact (minpoly.two_le_natDegree_iff hint).mpr hx

/-- `K` has an element outside `ℚ`. -/
theorem exists_not_mem_range (hK : Module.finrank ℚ K = 2) :
    ∃ α : K, α ∉ (algebraMap ℚ K).range := by
  by_contra h
  push Not at h
  have htop : (⊤ : IntermediateField ℚ K) = ⊥ := by
    rw [eq_bot_iff]
    intro x _
    obtain ⟨r, rfl⟩ := h x
    exact IntermediateField.algebraMap_mem _ r
  have := IntermediateField.finrank_top' (F := ℚ) (E := K)
  rw [htop, IntermediateField.finrank_bot, hK] at this
  norm_num at this

/-- **`K = ℚ(√m)`**: some `θ ∈ 𝓞_K` outside `ℚ` has `θ² = m` with `m` a squarefree integer. -/
theorem exists_sqrt_gen (hK : Module.finrank ℚ K = 2) :
    ∃ (θ : 𝓞 K) (m : ℤ), Squarefree m ∧ (θ : K) ^ 2 = m ∧ (θ : K) ∉ (algebraMap ℚ K).range := by
  obtain ⟨α, hα⟩ := exists_not_mem_range hK
  have hint : IsIntegral ℚ α := .of_finite ℚ α
  have hdeg : (minpoly ℚ α).natDegree = 2 := le_antisymm
    ((minpoly.natDegree_le α).trans hK.le) ((minpoly.two_le_natDegree_iff hint).mpr hα)
  set c := (minpoly ℚ α).coeff 1
  set e := (minpoly ℚ α).coeff 0
  have hα2 : α ^ 2 + (c : K) * α + e = 0 := by
    have h := minpoly.aeval ℚ α
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, show (minpoly ℚ α).coeff 2 = 1 by
        rw [← hdeg]; exact minpoly.monic hint] at h
    simp only [pow_zero, pow_one, Algebra.smul_def, mul_one] at h
    rw [← h]
    simp only [c, e, eq_ratCast]
    ring
  -- `β = 2α + c`, `β² = c² − 4e`
  set β : K := 2 * α + c
  have hβ2 : β ^ 2 = ((c ^ 2 - 4 * e : ℚ) : K) := by
    push_cast
    linear_combination 4 * hα2
  have hβ : β ∉ (algebraMap ℚ K).range := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨(r - c) / 2, ?_⟩
    rw [map_div₀, map_sub, hr, map_ofNat]
    simp only [β, eq_ratCast]
    field_simp
    ring
  set r : ℚ := c ^ 2 - 4 * e
  have hr0 : r ≠ 0 := by
    intro h0
    have : β ^ 2 = 0 := by rw [hβ2, h0]; simp
    exact hβ ⟨0, by rw [map_zero]; exact ((pow_eq_zero_iff two_ne_zero).mp this).symm⟩
  -- clear the denominator: `(d β)² = n d`
  set N : ℤ := r.num * r.den
  have hN : (((r.den : ℚ) • β) : K) ^ 2 = (N : K) := by
    rw [_root_.smul_pow, hβ2, Algebra.smul_def, ← eq_ratCast (algebraMap ℚ K) r, ← map_mul]
    have : ((r.den : ℚ) ^ 2 * r) = (N : ℚ) := by
      simp only [N, Int.cast_mul, Int.cast_natCast]
      rw [sq, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [this, map_intCast]
  obtain ⟨s, m, hsm, hm⟩ := exists_sq_mul_squarefree N
  have hN0 : N ≠ 0 := by
    simp only [N]
    exact mul_ne_zero (Rat.num_ne_zero.mpr hr0) (by exact_mod_cast r.den_nz)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hN0
    rw [← hsm]
    simp
  set θ₀ : K := ((r.den : ℚ) • β) / s
  have hθ₀ : θ₀ ^ 2 = m := by
    have hs : (s : K) ≠ 0 := by exact_mod_cast hs0
    rw [div_pow, hN, ← hsm]
    push_cast
    field_simp
  have hθ₀int : IsIntegral ℤ θ₀ := by
    refine ⟨X ^ 2 - C m, by monicity!, ?_⟩
    rw [← aeval_def]
    rw [map_sub, map_pow, aeval_X, aeval_C, hθ₀, algebraMap_int_eq, eq_intCast, sub_self]
  have hθ₀r : θ₀ ∉ (algebraMap ℚ K).range := by
    rintro ⟨t, ht⟩
    apply hβ
    refine ⟨t * s / r.den, ?_⟩
    have hd : ((r.den : ℚ) : K) ≠ 0 := by exact_mod_cast r.den_nz
    have hs : (s : K) ≠ 0 := by exact_mod_cast hs0
    rw [map_div₀, map_mul, ht]
    simp only [θ₀, Algebra.smul_def, eq_ratCast, map_intCast, map_natCast]
    field_simp
  exact ⟨⟨θ₀, hθ₀int⟩, m, hm, hθ₀, hθ₀r⟩

/-- **`disc K = (u² − 4v) q²`** for a generator `θ ∈ 𝓞_K` with `minpoly ℚ θ = X² + uX + v`
(change of basis from the power basis `(1, θ)` to an integral basis). -/
theorem discr_eq_mul_sq (hK : Module.finrank ℚ K = 2) {θ : 𝓞 K} {u v : ℤ}
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    ∃ q : ℚ, (discr K : ℚ) = ((u ^ 2 - 4 * v : ℤ) : ℚ) * q ^ 2 := by
  classical
  set b := (pbOf hK hmin).basis
  set b' := integralBasis K
  have hcard : Fintype.card (Fin (pbOf hK hmin).dim) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis b']
  let e := Fintype.equivOfCardEq hcard
  set c := b.reindex e
  set P := c.toMatrix b'
  have hb' : (⇑b') = Matrix.vecMul (⇑c) (P.map (algebraMap ℚ K)) := by
    funext j
    rw [Matrix.vecMul, dotProduct]
    simp only [Matrix.map_apply]
    rw [← c.sum_toMatrix_smul_self b' j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
  refine ⟨P.det, ?_⟩
  have hc : Algebra.discr ℚ ⇑c = Algebra.discr ℚ ⇑b := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
  rw [coe_discr, hb', Algebra.discr_of_matrix_vecMul, hc, discr_pbOf, mul_comm]

/-! ### The arithmetic of the two cases -/

/-- Clearing the denominator of `q` in `D = A q²`: `D d² = A n²` with `n, d` coprime. -/
theorem clear_den {D A : ℤ} {q : ℚ} (h : (D : ℚ) = A * q ^ 2) :
    D * (q.den : ℤ) ^ 2 = A * q.num ^ 2 := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have : (D : ℚ) * (q.den : ℚ) ^ 2 = A * (q.num : ℚ) ^ 2 := by
    rw [h]
    nth_rewrite 1 [← Rat.num_div_den q]
    field_simp
  exact_mod_cast this

theorem coprime_num_den (q : ℚ) {p : ℤ} (hp : Prime p) (h1 : p ∣ q.num) (h2 : p ∣ (q.den : ℤ)) :
    False := by
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact q.reduced
  exact hp.not_unit (hcop.isUnit_of_dvd' h1 h2)

/-- **Odd `p`**: if `D = 4m q²` with `m` squarefree, `p ∤ D` and `D` a square mod `p`, then
`p ∤ m` and `m` is a square mod `p`. -/
theorem odd_case {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {D m : ℤ} (hm : Squarefree m)
    {q : ℚ} (h : (D : ℚ) = ((4 * m : ℤ) : ℚ) * q ^ 2) (hpD : ¬ (p : ℤ) ∣ D)
    (hsq : IsSquare (D : ZMod p)) : ¬ (p : ℤ) ∣ m ∧ IsSquare (m : ZMod p) := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcl := clear_den h
  have hp4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have : (p : ℤ) ∣ 2 ^ 2 := by norm_num; exact h4
    have h2 : (p : ℤ) ∣ 2 := hprime.dvd_of_dvd_pow this
    have : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hn : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have : (p : ℤ) ∣ D * (q.den : ℤ) ^ 2 := by
      rw [hcl]; exact dvd_mul_of_dvd_right (dvd_pow hn two_ne_zero) _
    rcases hprime.dvd_or_dvd this with h1 | h1
    · exact hpD h1
    · exact coprime_num_den q hprime hn (hprime.dvd_of_dvd_pow h1)
  have hd : ¬ (p : ℤ) ∣ (q.den : ℤ) := by
    intro hd
    have h1 : (p : ℤ) ^ 2 ∣ 4 * m * q.num ^ 2 := by
      rw [← hcl]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd 2) _
    have hcop : IsCoprime ((p : ℤ) ^ 2) (4 * q.num ^ 2) := by
      apply IsCoprime.pow_left
      rw [Irreducible.coprime_iff_not_dvd hprime.irreducible]
      intro h'
      rcases hprime.dvd_or_dvd h' with h' | h'
      · exact hp4 h'
      · exact hn (hprime.dvd_of_dvd_pow h')
    have h2 : (p : ℤ) ^ 2 ∣ m := by
      rw [show 4 * m * q.num ^ 2 = m * (4 * q.num ^ 2) by ring] at h1
      exact hcop.dvd_of_dvd_mul_right h1
    have := hm (p : ℤ) (by rw [← sq]; exact h2)
    exact hprime.not_isUnit this
  have hmp : ¬ (p : ℤ) ∣ m := by
    intro hmp
    have : (p : ℤ) ∣ D * (q.den : ℤ) ^ 2 := by
      rw [hcl]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hmp _) _
    rcases hprime.dvd_or_dvd this with h1 | h1
    · exact hpD h1
    · exact hd (hprime.dvd_of_dvd_pow h1)
  refine ⟨hmp, ?_⟩
  obtain ⟨t, ht⟩ := hsq
  have hcast : (D : ZMod p) * (q.den : ZMod p) ^ 2 = 4 * (m : ZMod p) * (q.num : ZMod p) ^ 2 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) hcl
  have hn' : (q.num : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2' : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  refine ⟨t * q.den / (2 * q.num), ?_⟩
  field_simp
  rw [ht] at hcast
  linear_combination -hcast

/-- Odd integers have square `≡ 1 (mod 8)`. -/
theorem sq_zmod8_of_odd {k : ℤ} (hk : k % 2 = 1) : ((k : ZMod 8)) ^ 2 = 1 := by
  have h : ∀ x : ZMod 8, x.val % 2 = 1 → x ^ 2 = 1 := by decide
  apply h
  have h1 := ZMod.val_intCast (n := 8) k
  omega

/-- **`p = 2`**: if `D = 4m q²` with `m` squarefree and `D ≡ 1 (mod 8)`, then `m ≡ 1 (mod 8)`. -/
theorem two_case {D m : ℤ} (hm : Squarefree m) {q : ℚ} (h : (D : ℚ) = ((4 * m : ℤ) : ℚ) * q ^ 2)
    (hD : D % 8 = 1) : m % 8 = 1 := by
  have hcl := clear_den h
  have hprime : Prime (2 : ℤ) := Int.prime_two
  -- `q.den` is even
  have hd2 : (2 : ℤ) ∣ (q.den : ℤ) := by
    have : (2 : ℤ) ∣ D * (q.den : ℤ) ^ 2 := by
      rw [hcl]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _
    rcases hprime.dvd_or_dvd this with h1 | h1
    · omega
    · exact hprime.dvd_of_dvd_pow h1
  obtain ⟨d', hd'⟩ := hd2
  have hn2 : q.num % 2 = 1 := by
    by_contra hn
    exact coprime_num_den q hprime (by omega) ⟨d', hd'⟩
  have hcl' : D * d' ^ 2 = m * q.num ^ 2 := by
    rw [hd'] at hcl
    have h4 : 4 * (D * d' ^ 2) = 4 * (m * q.num ^ 2) := by linear_combination hcl
    exact (mul_right_inj' (by norm_num : (4 : ℤ) ≠ 0)).mp h4
  -- `d'` is odd
  have hd'2 : d' % 2 = 1 := by
    by_contra hd''
    have h4 : (2 : ℤ) ^ 2 ∣ m * q.num ^ 2 := by
      rw [← hcl']; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (by omega) 2) _
    have hcop : IsCoprime ((2 : ℤ) ^ 2) (q.num ^ 2) := by
      apply IsCoprime.pow
      rw [Irreducible.coprime_iff_not_dvd hprime.irreducible]
      omega
    have := hm 2 (by rw [← sq]; exact hcop.dvd_of_dvd_mul_right h4)
    exact hprime.not_isUnit this
  have hcast : (D : ZMod 8) * (d' : ZMod 8) ^ 2 = (m : ZMod 8) * (q.num : ZMod 8) ^ 2 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 8) hcl'
  rw [sq_zmod8_of_odd hd'2, sq_zmod8_of_odd hn2, mul_one, mul_one] at hcast
  have h1 : (((D : ZMod 8)).val : ℤ) = ((m : ZMod 8)).val := by rw [hcast]
  rw [ZMod.val_intCast, ZMod.val_intCast] at h1
  omega

/-! ### The splitting criterion -/

/-- **The splitting criterion** (`GenusOdd.SplittingCriterion`; PROVED). -/
theorem splittingCriterion_proof : GenusOdd.SplittingCriterion := by
  intro K _ _ hK p hp hsq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpD, h2, hodd⟩ := hsq
  obtain ⟨θ, m, hm, hθ2, hθr⟩ := exists_sqrt_gen hK
  have hmin : minpoly ℚ (θ : K) = X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((-m : ℤ) : ℚ) :=
    minpoly_eq_of_aeval hK hθr 0 (-m) (by rw [hθ2]; push_cast; ring)
  obtain ⟨q, hq⟩ := discr_eq_mul_sq hK hmin
  have hq' : (discr K : ℚ) = ((4 * m : ℤ) : ℚ) * q ^ 2 := by rw [hq]; push_cast; ring
  by_cases hp2 : p = 2
  · -- `p = 2`: the generator `(1 + θ)/2`
    subst hp2
    have hm8 := two_case hm hq' (h2 rfl)
    set t := m / 8
    have hmt : m = 8 * t + 1 := by omega
    set θ' : K := (1 + θ) / 2
    have hθ'2 : θ' ^ 2 + ((-1 : ℤ) : K) * θ' + ((-2 * t : ℤ) : K) = 0 := by
      simp only [θ']
      push_cast
      have : ((θ : K)) ^ 2 = 8 * (t : K) + 1 := by rw [hθ2, hmt]; push_cast; ring
      field_simp
      linear_combination this
    have hθ'int : IsIntegral ℤ θ' := by
      refine ⟨X ^ 2 + C (-1 : ℤ) * X + C (-2 * t : ℤ), by monicity!, ?_⟩
      rw [← aeval_def]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq]
      convert hθ'2 using 2 <;> simp
    have hθ'r : θ' ∉ (algebraMap ℚ K).range := by
      rintro ⟨r, hr⟩
      apply hθr
      refine ⟨2 * r - 1, ?_⟩
      rw [map_sub, map_mul, hr, map_ofNat, map_one]
      simp only [θ']
      field_simp
      ring
    let θ'' : 𝓞 K := ⟨θ', hθ'int⟩
    have hmin' : minpoly ℚ (θ'' : K) = X ^ 2 + C ((-1 : ℤ) : ℚ) * X + C ((-2 * t : ℤ) : ℚ) :=
      minpoly_eq_of_aeval hK hθ'r (-1) (-2 * t) hθ'2
    refine splitsIn_of_factor hK hmin' (p := 2) ?_ 0 1 (by norm_num) ?_ (by norm_num)
    · rw [show (-1 : ℤ) ^ 2 - 4 * (-2 * t) = m by rw [hmt]; ring]
      intro h; push_cast at h; omega
    · exact ⟨-t, by push_cast; ring⟩
  · -- odd `p`: the generator `θ`
    have hpD' : ¬ (p : ℤ) ∣ discr K := hpD
    obtain ⟨hmp, ⟨r, hr⟩⟩ := odd_case hp2 hm hq' hpD' (hodd hp2)
    refine splitsIn_of_factor hK hmin (p := p) ?_ (r.val : ℤ) (-(r.val : ℤ)) (by simp) ?_ ?_
    · rw [show (0 : ℤ) ^ 2 - 4 * (-m) = 4 * m by ring]
      intro h
      have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hprime.dvd_or_dvd h with h4 | h4
      · have : (p : ℤ) ∣ 2 ^ 2 := by norm_num; exact h4
        have h2' : p ∣ 2 := by exact_mod_cast hprime.dvd_of_dvd_pow this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
      · exact hmp h4
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hr]
      ring
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      intro h0
      have hr0 : r ≠ 0 := by
        rintro rfl
        apply hmp
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hr, mul_zero]
      have h2' : (2 : ZMod p) ≠ 0 := by
        intro h0
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      have : (2 : ZMod p) * r = 0 := by linear_combination -h0
      rcases mul_eq_zero.mp this with h | h
      · exact h2' h
      · exact hr0 h

end ZInQ.Contrib.CloudB3RC53.Splitting
