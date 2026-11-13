import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/Chi.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the Dirichlet character `χ` of B2 (N5 L671-677)

N5 takes `T₋` to be the finite primes where the invariant of `[ε]` is `1/2`, picks an odd
character of `(ℤ/p)^×` at each odd `p ∈ T₋` and the nontrivial character mod `4` if `2 ∈ T₋`,
multiplies them to `χ`, and bounds the order `m ≤ 2 ∏_{p∈T, p≠2}(p-1)` (paraphrase).

Proved here over Mathlib's `DirichletCharacter` (genuine definitions), for any finite set `T`
of primes and any subset `T₋ ⊆ T`:

* `exists_odd_char`: for `n > 2` there is a Dirichlet character mod `n` with `χ(-1) = -1`
  (at `n = 4` it is the nontrivial character mod four);
* `exists_chi`: the product `χ = ∏_{p ∈ T₋} χ_p` (each `χ_p` odd of level `p`, or `4` at `p = 2`,
  raised to the level `N = ∏_{p ∈ T₋} lev p`) has level supported in `T` and
  `orderOf χ ≤ 2 ∏_{p ∈ T, p ≠ 2} (p - 1)`.

Not here: that the local invariant of `δχ` at `p` is `1/2` exactly when `χ_p(-1) = -1` (local
class field theory; leaf L-B2c of `docs/research/glue-descent.md`).
-/

namespace GlueDescent

open scoped Nat

/-- The local level: `4` at `p = 2`, `p` at odd `p`. -/
def lev (p : ℕ) : ℕ := if p = 2 then 4 else p

theorem two_lt_lev {p : ℕ} (hp : p.Prime) : 2 < lev p := by
  unfold lev
  split_ifs with h
  · norm_num
  · have := hp.two_le; omega

theorem totient_lev {p : ℕ} (hp : p.Prime) : φ (lev p) = if p = 2 then 2 else p - 1 := by
  unfold lev
  split_ifs with h
  · decide
  · exact Nat.totient_prime hp

/-- For `n > 2` there is a Dirichlet character mod `n` that is odd: `χ(-1) = -1`. -/
theorem exists_odd_char (n : ℕ) (hn : 2 < n) : ∃ χ : DirichletCharacter ℂ n, χ (-1) = -1 := by
  haveI : Fact (2 < n) := ⟨hn⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero ((Monoid.exponent (ZMod n)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := (ZMod n)ˣ))⟩
  obtain ⟨χ, hχ⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) ℂ (ZMod.neg_one_ne_one (n := n))
  refine ⟨χ, ?_⟩
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h hχ
  · exact h

/-- The order of a Dirichlet character mod `n` divides `φ(n)`. -/
theorem orderOf_dvd_totient {n : ℕ} (χ : DirichletCharacter ℂ n) : orderOf χ ∣ φ n := by
  apply orderOf_dvd_of_pow_eq_one
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, map_one]

/-- In a commutative monoid, the order of a finite product divides the product of the orders. -/
theorem orderOf_prod_dvd {M ι : Type*} [CommMonoid M] (s : Finset ι) (x : ι → M) :
    orderOf (∏ i ∈ s, x i) ∣ ∏ i ∈ s, orderOf (x i) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => orderOf (x i)) hi
  rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]

/-- The chosen odd character of level `lev p`. -/
noncomputable def oddChar (p : ℕ) : DirichletCharacter ℂ (lev p) :=
  if h : 2 < lev p then Classical.choose (exists_odd_char _ h) else 1

theorem oddChar_neg_one {p : ℕ} (hp : p.Prime) : oddChar p (-1) = -1 := by
  unfold oddChar
  rw [dif_pos (two_lt_lev hp)]
  exact Classical.choose_spec (exists_odd_char _ (two_lt_lev hp))

/-- The level `N = ∏_{p ∈ T₋} lev p` of `χ`. -/
def chiLevel (Tm : Finset ℕ) : ℕ := ∏ p ∈ Tm, lev p

theorem lev_dvd_chiLevel {Tm : Finset ℕ} {p : ℕ} (hp : p ∈ Tm) : lev p ∣ chiLevel Tm :=
  Finset.dvd_prod_of_mem lev hp

/-- `χ = ∏_{p ∈ T₋} χ_p`, raised to level `N`. -/
noncomputable def chi (Tm : Finset ℕ) : DirichletCharacter ℂ (chiLevel Tm) :=
  ∏ p ∈ Tm.attach, DirichletCharacter.changeLevel (lev_dvd_chiLevel p.2) (oddChar p.1)

/-- The arithmetic of the order bound: `∏_{p ∈ T₋} φ(lev p) ≤ 2 ∏_{p ∈ T, p ≠ 2} (p - 1)`. -/
theorem prod_totient_lev_le (T Tm : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (hTm : Tm ⊆ T) :
    ∏ p ∈ Tm, φ (lev p) ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
  rw [Finset.prod_congr rfl (fun p hp => totient_lev (hT p (hTm hp))),
    ← Finset.prod_filter_mul_prod_filter_not Tm (· = 2)]
  apply Nat.mul_le_mul
  · -- the factor at 2 is at most 2
    have hsub : Tm.filter (· = 2) ⊆ {2} := by
      intro p hp; rw [Finset.mem_filter] at hp; simp [hp.2]
    calc ∏ p ∈ Tm.filter (· = 2), (if p = 2 then 2 else p - 1)
        = ∏ p ∈ Tm.filter (· = 2), 2 :=
          Finset.prod_congr rfl (fun p hp => by rw [if_pos (Finset.mem_filter.mp hp).2])
      _ ≤ ∏ p ∈ ({2} : Finset ℕ), 2 :=
          Finset.prod_le_prod_of_subset_of_one_le hsub (fun _ _ _ => by norm_num)
      _ = 2 := by simp
  · calc ∏ p ∈ Tm.filter (fun p => ¬ p = 2), (if p = 2 then 2 else p - 1)
        = ∏ p ∈ Tm.filter (fun p => ¬ p = 2), (p - 1) :=
          Finset.prod_congr rfl (fun p hp => by rw [if_neg (Finset.mem_filter.mp hp).2])
      _ ≤ ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
          apply Finset.prod_le_prod_of_subset_of_one_le
          · intro p hp
            rw [Finset.mem_filter] at hp ⊢
            exact ⟨hTm hp.1, hp.2⟩
          · intro p hp _
            have := (hT p (Finset.mem_filter.mp hp).1).two_le
            omega

/-- **B2, the character `χ`** (N5 L671-677). For a finite set `T` of primes and `T₋ ⊆ T`,
the character `χ = ∏_{p ∈ T₋} χ_p` with each `χ_p` odd of level `lev p` has level divisible
only by primes of `T`, and order at most `2 ∏_{p ∈ T, p ≠ 2} (p - 1)`. -/
theorem exists_chi (T Tm : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (hTm : Tm ⊆ T) :
    (∀ p ∈ Tm, oddChar p (-1) = -1) ∧
    (∀ q : ℕ, q.Prime → q ∣ chiLevel Tm → q ∈ T) ∧
    orderOf (chi Tm) ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
  refine ⟨fun p hp => oddChar_neg_one (hT p (hTm hp)), ?_, ?_⟩
  · intro q hq hdvd
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hdvd
    have hpT := hT p (hTm hp)
    unfold lev at hqp
    split_ifs at hqp with h2
    · subst h2
      have : q ∣ 2 := hq.prime.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by norm_num at hqp ⊢; exact hqp)
      rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this]
      exact hTm hp
    · rw [(Nat.prime_dvd_prime_iff_eq hq hpT).mp hqp]
      exact hTm hp
  · have hpos : 0 < ∏ p ∈ Tm, φ (lev p) := by
      apply Finset.prod_pos
      intro p hp
      exact Nat.totient_pos.mpr (by have := two_lt_lev (hT p (hTm hp)); omega)
    calc orderOf (chi Tm) ≤ ∏ p ∈ Tm, φ (lev p) := by
          apply Nat.le_of_dvd hpos
          refine (orderOf_prod_dvd _ _).trans ?_
          rw [← Finset.prod_attach Tm (fun p => φ (lev p))]
          apply Finset.prod_dvd_prod_of_dvd
          intro p _
          exact (orderOf_map_dvd _ _).trans (orderOf_dvd_totient _)
      _ ≤ _ := prod_totient_lev_le T Tm hT hTm

end GlueDescent

