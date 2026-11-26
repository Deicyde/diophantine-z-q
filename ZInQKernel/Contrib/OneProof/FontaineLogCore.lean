import Mathlib

/-!
# `log [p̃]` is not in the fraction field of `W(R)[ξ/p]` (Fontaine, Lemme 4.3.1)

Reference: J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II,
4.3.1 (statement) and 4.3.2 (proof), pp. 87-88; used in Brinon-Conrad, *CMI summer school notes on
p-adic Hodge theory* (preliminary version, June 24, 2009), proof of Thm 9.2.10, p. 143.

Fontaine's argument uses no Frobenius. With `ξ = p − [p̃]`, `β = ξ/p` and `S` the ring of all sums
`Σ_{n ≥ 0} a_n β^n` (`a_n ∈ W(R)`, taken in `B_dR^+`), `u = log([p̃]/p) = −Σ_{n ≥ 1} β^n/n`
satisfies `a·u ∉ S` for every nonzero `a ∈ S`. The inputs are that `S` is `p`-adically separated
and that `S ∩ Fil^i = β^i S`.

Here it is proved for an `A`-algebra `P` (in the application `A = W(𝓞_{ℂ_p}^♭)`, `P = A[1/p]`),
an ideal `I` of `P` (`ker θ`) and the `I`-adic completion `AdicCompletion I P` (Mathlib's
`B_dR^+`). The hypotheses are facts about `W(𝓞_{ℂ_p}^♭)`: `ξ ∈ I`, `p β = ξ`, `β ∈ I`,
`p · pinv = 1`, `n · inv n = 1` for `n ≠ 0`, `p^{v_p(n)}/n ∈ A` for `n ≠ 0`, `A ∩ I^k = ξ^k A`,
`⋂_k (p^k A + ξ^m A) = ξ^m A`, and `ξ` is a non-zero-divisor of the completion.
-/

noncomputable section

open PowerSeries

namespace FontaineLogCore

/-! ## §1. Power-series evaluation at an element of `I` in the `I`-adic completion -/

section PSEval

variable {P : Type*} [CommRing P] (I : Ideal P) {x : P}

theorem eval_mem_pow_of_coeff (hx : x ∈ I) (n : ℕ) (Q : Polynomial P)
    (hQ : ∀ k < n, Q.coeff k = 0) : Q.eval x ∈ I ^ n := by
  have hdvd : (Polynomial.X : Polynomial P) ^ n ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    exact hQ
  obtain ⟨R, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

theorem eval_sub_trunc_mem (hx : x ∈ I) (n : ℕ) (Q : Polynomial P) :
    Q.eval x - (trunc n (Q : P⟦X⟧)).eval x ∈ I ^ n := by
  rw [← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hk, Polynomial.coeff_coe, sub_self]

theorem trunc_cauchy (hx : x ∈ I) (f : P⟦X⟧) (n : ℕ) :
    (trunc n f).eval x ≡ (trunc (n + 1) f).eval x [SMOD (I ^ n • ⊤ : Submodule P P)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, ite_eq_left hk, ite_eq_left (by omega), sub_self]

/-- The `I`-adic limit of the truncations `Σ_{k<n} a_k x^k`. -/
def psEvalFun (hx : x ∈ I) (f : P⟦X⟧) : AdicCompletion I P :=
  AdicCompletion.mk I P (AdicCompletion.AdicCauchySequence.mk I P
    (fun n => (trunc n f).eval x) (trunc_cauchy I hx f))

theorem evalₐ_psEvalFun (hx : x ∈ I) (f : P⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEvalFun I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) := by
  unfold psEvalFun
  rw [AdicCompletion.evalₐ_mk]
  rfl

theorem mk_eval_trunc (hx : x ∈ I) (n : ℕ) (Q : Polynomial P) :
    Ideal.Quotient.mk (I ^ n) ((trunc n (Q : P⟦X⟧)).eval x) = Ideal.Quotient.mk (I ^ n) (Q.eval x) := by
  rw [Ideal.Quotient.eq]
  have := eval_sub_trunc_mem I hx n Q
  rw [← neg_sub]
  exact Submodule.neg_mem _ this

/-- **Evaluation at `x ∈ I`**, `P⟦X⟧ → P̂_I`, `Σ a_k X^k ↦ Σ a_k x^k`. -/
def psEval (hx : x ∈ I) : P⟦X⟧ →+* AdicCompletion I P where
  toFun := psEvalFun I hx
  map_one' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_one (AdicCompletion.evalₐ I n), ← Polynomial.coe_one, mk_eval_trunc I hx,
      Polynomial.eval_one, map_one]
  map_mul' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_mul (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      ← trunc_trunc_mul_trunc,
      ← Polynomial.coe_mul, mk_eval_trunc I hx, Polynomial.eval_mul, map_mul]
  map_zero' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_zero (AdicCompletion.evalₐ I n), map_zero (trunc n),
      Polynomial.eval_zero, map_zero]
  map_add' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_add (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      map_add (trunc n), Polynomial.eval_add, map_add]

theorem evalₐ_psEval (hx : x ∈ I) (f : P⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEval I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) :=
  evalₐ_psEvalFun I hx f n

theorem psEval_C (hx : x ∈ I) (a : P) :
    psEval I hx (C a) = algebraMap P (AdicCompletion I P) a := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, ← Polynomial.coe_C, mk_eval_trunc I hx, Polynomial.eval_C]
  simp

theorem evalₐ_algebraMap (n : ℕ) (y : P) :
    AdicCompletion.evalₐ I n (algebraMap P (AdicCompletion I P) y) = Ideal.Quotient.mk (I ^ n) y :=
  AdicCompletion.evalₐ_of I n y

theorem psEval_polynomial (hx : x ∈ I) (Q : Polynomial P) :
    psEval I hx (Q : P⟦X⟧) = algebraMap P (AdicCompletion I P) (Q.eval x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, mk_eval_trunc I hx, evalₐ_algebraMap]

theorem psEval_X (hx : x ∈ I) : psEval I hx PowerSeries.X = algebraMap P (AdicCompletion I P) x := by
  rw [← Polynomial.coe_X, psEval_polynomial I hx, Polynomial.eval_X]

end PSEval

/-! ## §2. Fontaine's Lemme 4.3.1 -/

section Core

variable (A : Type*) {P : Type*} [CommRing A] [CommRing P] [Algebra A P] (I : Ideal P) (p : ℕ)

/-- `S = A[β]`: all `Σ a_n β^n`, `a_n ∈ A`, in the completion. -/
def SubS {β : P} (hβI : β ∈ I) : Subring (AdicCompletion I P) :=
  ((psEval I hβI).comp (PowerSeries.map (algebraMap A P))).range

theorem mem_subS {β : P} (hβI : β ∈ I) (y : AdicCompletion I P) :
    y ∈ SubS A I hβI ↔ ∃ f : A⟦X⟧, psEval I hβI (PowerSeries.map (algebraMap A P) f) = y :=
  RingHom.mem_range

theorem psEval_map_mem {β : P} (hβI : β ∈ I) (f : A⟦X⟧) :
    psEval I hβI (PowerSeries.map (algebraMap A P) f) ∈ SubS A I hβI :=
  (mem_subS A I hβI _).mpr ⟨f, rfl⟩

theorem cancel_p_pow {pinv : P} (hpinv : (p : P) * pinv = 1) {x y : P} (k : ℕ)
    (h : (p : P) ^ k * x = (p : P) ^ k * y) : x = y := by
  have e : pinv ^ k * (p : P) ^ k = 1 := by rw [← mul_pow, mul_comm pinv, hpinv, one_pow]
  calc x = pinv ^ k * ((p : P) ^ k * x) := by rw [← mul_assoc, e, one_mul]
    _ = pinv ^ k * ((p : P) ^ k * y) := by rw [h]
    _ = y := by rw [← mul_assoc, e, one_mul]

theorem pow_mul_trunc_eval {β : P} (ξ : A) (hpβ : (p : P) * β = algebraMap A P ξ) (f : A⟦X⟧)
    (m : ℕ) :
    (p : P) ^ m * (trunc m (PowerSeries.map (algebraMap A P) f)).eval β =
      algebraMap A P (∑ i ∈ Finset.range m, PowerSeries.coeff i f * ξ ^ i * (p : A) ^ (m - i)) := by
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := (Finset.mem_range.mp hi).le
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  have hm : (p : P) ^ m = (p : P) ^ (m - i) * (p : P) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hm, ← hpβ]
  ring

theorem s_mod {β : P} (hβI : β ∈ I) (ξ : A) (hpβ : (p : P) * β = algebraMap A P ξ) (f : A⟦X⟧)
    (m : ℕ) :
    ∃ w : A, AdicCompletion.evalₐ I m ((p : AdicCompletion I P) ^ m *
      psEval I hβI (PowerSeries.map (algebraMap A P) f)) =
        Ideal.Quotient.mk (I ^ m) (algebraMap A P w) := by
  refine ⟨∑ i ∈ Finset.range m, PowerSeries.coeff i f * ξ ^ i * (p : A) ^ (m - i), ?_⟩
  rw [map_mul, evalₐ_psEval, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (I ^ m)),
    ← map_pow, ← map_mul, pow_mul_trunc_eval A p ξ hpβ f m]

/-- **`S` is `p`-adically separated** (Fontaine 4.3.2: "S est séparé pour la topologie p-adique"). -/
theorem s_sep {β : P} (hβI : β ∈ I) (ξ : A) {pinv : P} (hpβ : (p : P) * β = algebraMap A P ξ)
    (hpinv : (p : P) * pinv = 1) (hξI : algebraMap A P ξ ∈ I)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (hsepA : ∀ (m : ℕ) (w : A), (∀ k : ℕ, ∃ a b : A, w = (p : A) ^ k * a + ξ ^ m * b) →
      w ∈ Ideal.span {ξ ^ m})
    (x : AdicCompletion I P)
    (h : ∀ k : ℕ, ∃ y ∈ SubS A I hβI, x = (p : AdicCompletion I P) ^ k * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  rw [map_zero]
  choose y hy hxy using h
  choose f hf using fun k => (mem_subS A I hβI (y k)).mp (hy k)
  choose w hw using fun k => s_mod A I p hβI ξ hpβ (f k) m
  have hk : ∀ k, AdicCompletion.evalₐ I m ((p : AdicCompletion I P) ^ m * x) =
      Ideal.Quotient.mk (I ^ m) (algebraMap A P ((p : A) ^ k * w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, ← hf k, hw k, map_pow, map_natCast, map_mul, map_pow,
      map_natCast, map_mul, map_pow, map_natCast]
  have hw0 : w 0 ∈ Ideal.span {ξ ^ m} := by
    refine hsepA m (w 0) fun k => ?_
    have e := (hk 0).symm.trans (hk k)
    rw [Ideal.Quotient.eq, ← map_sub] at e
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hξpow m _ e)
    exact ⟨w k, b, by rw [pow_zero, one_mul] at hb; linear_combination -hb⟩
  have h0 : AdicCompletion.evalₐ I m ((p : AdicCompletion I P) ^ m * x) = 0 := by
    rw [hk 0, pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    rw [← hc, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hξI m)
  rw [map_mul, map_pow, map_natCast] at h0
  have hu : IsUnit ((p : P ⧸ I ^ m) ^ m) := by
    refine IsUnit.pow _ ?_
    have he : (p : P ⧸ I ^ m) * Ideal.Quotient.mk (I ^ m) pinv = 1 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), ← map_mul, hpinv, map_one]
    exact ⟨⟨_, _, he, by rwa [mul_comm]⟩, rfl⟩
  exact (hu.mul_right_eq_zero).mp h0

/-- **`S ∩ Fil^i = β^i S`** (Fontaine 4.3.2: "Fil^i S est l'idéal principal engendré par β^i"). -/
theorem s_fil {β : P} (hβI : β ∈ I) (ξ : A) {pinv : P} (hpβ : (p : P) * β = algebraMap A P ξ)
    (hpinv : (p : P) * pinv = 1)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (f : A⟦X⟧) (i : ℕ)
    (h : AdicCompletion.evalₐ I i (psEval I hβI (PowerSeries.map (algebraMap A P) f)) = 0) :
    ∃ g : A⟦X⟧, psEval I hβI (PowerSeries.map (algebraMap A P) f) =
      algebraMap P (AdicCompletion I P) β ^ i * psEval I hβI (PowerSeries.map (algebraMap A P) g) := by
  have hdec : PowerSeries.map (algebraMap A P) f =
      ((trunc i (PowerSeries.map (algebraMap A P) f) : Polynomial P) : P⟦X⟧) +
        PowerSeries.X ^ i * PowerSeries.map (algebraMap A P)
          (PowerSeries.mk fun k => PowerSeries.coeff (k + i) f) := by
    ext n
    rw [map_add, Polynomial.coeff_coe, coeff_trunc, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n < i
    · have h1 : ¬ i ≤ n := by omega
      rw [if_pos hn, if_neg h1, add_zero]
    · have h1 : i ≤ n := by omega
      rw [if_neg hn, if_pos h1, zero_add, PowerSeries.coeff_map, PowerSeries.coeff_map,
        PowerSeries.coeff_mk, Nat.sub_add_cancel h1]
  have hsplit : psEval I hβI (PowerSeries.map (algebraMap A P) f) =
      algebraMap P (AdicCompletion I P) ((trunc i (PowerSeries.map (algebraMap A P) f)).eval β) +
        algebraMap P (AdicCompletion I P) β ^ i *
          psEval I hβI (PowerSeries.map (algebraMap A P)
            (PowerSeries.mk fun k => PowerSeries.coeff (k + i) f)) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_mul, map_pow, psEval_X I hβI, psEval_polynomial I hβI]
  have hβi : (Ideal.Quotient.mk (I ^ i) β) ^ i = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hβI i
  have hQ : (trunc i (PowerSeries.map (algebraMap A P) f)).eval β ∈ I ^ i := by
    have h2 := congrArg (AdicCompletion.evalₐ I i) hsplit
    rw [h, map_add, map_mul, map_pow, evalₐ_algebraMap I, evalₐ_algebraMap I, hβi, zero_mul,
      add_zero] at h2
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2.symm
  have hw : algebraMap A P (∑ n ∈ Finset.range i, PowerSeries.coeff n f * ξ ^ n * (p : A) ^ (i - n))
      ∈ I ^ i := by
    rw [← pow_mul_trunc_eval A p ξ hpβ f i]
    exact Ideal.mul_mem_left _ _ hQ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hξpow i _ hw)
  have hQc : (trunc i (PowerSeries.map (algebraMap A P) f)).eval β = β ^ i * algebraMap A P c := by
    apply cancel_p_pow p hpinv i
    rw [pow_mul_trunc_eval A p ξ hpβ f i, ← hc, map_mul, map_pow, ← hpβ]
    ring
  refine ⟨PowerSeries.C c + PowerSeries.mk fun k => PowerSeries.coeff (k + i) f, ?_⟩
  rw [hsplit, hQc, map_add, map_add, PowerSeries.map_C, psEval_C I hβI, map_mul, map_pow]
  ring

/-- If every coefficient lies in `(p, ξ)`, the element lies in `p S`. -/
theorem mem_pS_of_coeff {β : P} (hβI : β ∈ I) (ξ : A) (hpβ : (p : P) * β = algebraMap A P ξ)
    (f : A⟦X⟧) (hf : ∀ n, PowerSeries.coeff n f ∈ Ideal.span {(p : A), ξ}) :
    ∃ y ∈ SubS A I hβI,
      psEval I hβI (PowerSeries.map (algebraMap A P) f) = (p : AdicCompletion I P) * y := by
  choose d e hde using fun n => Ideal.mem_span_pair.mp (hf n)
  refine ⟨psEval I hβI (PowerSeries.map (algebraMap A P)
    (PowerSeries.mk d + PowerSeries.X * PowerSeries.mk e)), psEval_map_mem A I hβI _, ?_⟩
  have hf' : f = PowerSeries.C (p : A) * PowerSeries.mk d + PowerSeries.C ξ * PowerSeries.mk e := by
    ext n
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, ← hde n]
    ring
  rw [hf']
  simp only [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_X, psEval_C, psEval_X, map_natCast]
  rw [← hpβ, map_mul, map_natCast]
  ring

/-- Split at the first coefficient outside `(p, ξ)`. -/
theorem decomp_min {β : P} (hβI : β ∈ I) (ξ : A) (hpβ : (p : P) * β = algebraMap A P ξ)
    (f : A⟦X⟧) (i : ℕ) (hi : ∀ n < i, PowerSeries.coeff n f ∈ Ideal.span {(p : A), ξ}) :
    ∃ s ∈ SubS A I hβI, psEval I hβI (PowerSeries.map (algebraMap A P) f) =
      (p : AdicCompletion I P) * s + algebraMap P (AdicCompletion I P) β ^ i *
        psEval I hβI (PowerSeries.map (algebraMap A P)
          (PowerSeries.mk fun k => PowerSeries.coeff (k + i) f)) := by
  classical
  have hgJ : ∀ n, PowerSeries.coeff n (PowerSeries.mk fun n =>
      if n < i then PowerSeries.coeff n f else 0) ∈ Ideal.span {(p : A), ξ} := by
    intro n
    rw [PowerSeries.coeff_mk]
    split_ifs with hn
    · exact hi n hn
    · exact Ideal.zero_mem _
  obtain ⟨s, hs, hgs⟩ := mem_pS_of_coeff A I p hβI ξ hpβ _ hgJ
  refine ⟨s, hs, ?_⟩
  have hdec : f = (PowerSeries.mk fun n => if n < i then PowerSeries.coeff n f else 0) +
      PowerSeries.X ^ i * PowerSeries.mk fun k => PowerSeries.coeff (k + i) f := by
    ext n
    rw [map_add, PowerSeries.coeff_X_pow_mul']
    simp only [PowerSeries.coeff_mk]
    by_cases hn : n < i
    · have h1 : ¬ i ≤ n := by omega
      rw [if_pos hn, if_neg h1, add_zero]
    · have h1 : i ≤ n := by omega
      rw [if_neg hn, if_pos h1, zero_add, Nat.sub_add_cancel h1]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, hgs, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_X, psEval_X I hβI]

theorem lt_pow_of_two_le {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : n < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 < q ^ n := pow_pos (by omega) n
    rw [pow_succ]
    calc n + 1 < q ^ n + q ^ n := by omega
      _ = q ^ n * 2 := by ring
      _ ≤ q ^ n * q := Nat.mul_le_mul le_rfl hq

/-- `−Σ_{n ≥ 1} X^n/n`. -/
def logNeg (inv : ℕ → P) : P⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else -inv n

/-- Fontaine's splitting `p^{j−1} u = (S-part) − β^{p^j}/p + β^{2p^j}(…)`. -/
theorem log_split [Fact p.Prime] {pinv : P} (hpinv : (p : P) * pinv = 1) (inv : ℕ → P)
    (hinv : ∀ n : ℕ, n ≠ 0 → (n : P) * inv n = 1)
    (hint : ∀ n : ℕ, n ≠ 0 → ∃ w : A, algebraMap A P w * (n : P) = (p : P) ^ padicValNat p n)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ (q : A⟦X⟧) (T : P⟦X⟧), PowerSeries.C ((p : P) ^ (j - 1)) * logNeg inv =
      PowerSeries.map (algebraMap A P) q - PowerSeries.C pinv * PowerSeries.X ^ (p ^ j) +
        PowerSeries.X ^ (2 * p ^ j) * T := by
  classical
  have hp := (Fact.out : p.Prime)
  have hN : 0 < p ^ j := pow_pos hp.pos j
  have hwex : ∀ n : ℕ, ∃ w : A, (n ≠ 0 → ¬ p ^ j ∣ n →
      algebraMap A P w = (p : P) ^ (j - 1) * inv n) := by
    intro n
    by_cases hn : n ≠ 0 ∧ ¬ p ^ j ∣ n
    · obtain ⟨w0, hw0⟩ := hint n hn.1
      have hv : padicValNat p n < j := by
        by_contra hc
        exact hn.2 ((padicValNat_dvd_iff_le hn.1).mpr (by omega))
      refine ⟨w0 * (p : A) ^ (j - 1 - padicValNat p n), fun _ _ => ?_⟩
      have hle : padicValNat p n ≤ j - 1 := by omega
      have e1 : (p : P) ^ (j - 1) = (p : P) ^ padicValNat p n * (p : P) ^ (j - 1 - padicValNat p n) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      have e2 := hinv n hn.1
      rw [map_mul, map_pow, map_natCast, e1, ← hw0]
      linear_combination (-(algebraMap A P w0) * (p : P) ^ (j - 1 - padicValNat p n)) * e2
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose w hw using hwex
  refine ⟨PowerSeries.mk fun n => if n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n then 0 else -w n,
    PowerSeries.mk fun n => -((p : P) ^ (j - 1) * inv (n + 2 * p ^ j)), ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, map_add, map_sub, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', logNeg]
  simp only [PowerSeries.coeff_mk]
  by_cases h0 : n = 0
  · subst h0
    have h1 : (0 : ℕ) ≠ p ^ j := by omega
    have h2 : ¬ 2 * p ^ j ≤ 0 := by omega
    simp [h1, h2]
  · by_cases hNn : n = p ^ j
    · subst hNn
      have h2 : ¬ 2 * p ^ j ≤ p ^ j := by omega
      have e3 : ((p ^ j : ℕ) : P) * inv (p ^ j) = 1 := hinv _ (by omega)
      have e4 : pinv ^ j * (p : P) ^ j = 1 := by rw [← mul_pow, mul_comm pinv, hpinv, one_pow]
      have e5 : inv (p ^ j) = pinv ^ j := by
        calc inv (p ^ j) = (pinv ^ j * (p : P) ^ j) * inv (p ^ j) := by rw [e4, one_mul]
          _ = pinv ^ j * (((p ^ j : ℕ) : P) * inv (p ^ j)) := by push_cast; ring
          _ = pinv ^ j := by rw [e3, mul_one]
      have e7 : pinv ^ j = pinv ^ (j - 1) * pinv := by rw [← pow_succ, Nat.sub_add_cancel hj]
      have e6 : (p : P) ^ (j - 1) * pinv ^ j = pinv := by
        rw [e7, ← mul_assoc, ← mul_pow, hpinv, one_pow, one_mul]
      have hor : p ^ j = 0 ∨ p ^ j = p ^ j ∨ 2 * p ^ j ≤ p ^ j := Or.inr (Or.inl rfl)
      rw [if_neg h0, if_pos hor, map_zero, if_pos rfl, if_neg h2, add_zero, zero_sub, mul_one, e5]
      linear_combination -e6
    · by_cases hbig : 2 * p ^ j ≤ n
      · have hor : n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n := Or.inr (Or.inr hbig)
        rw [if_neg h0, if_pos hor, map_zero, if_neg hNn, if_pos hbig, mul_zero, sub_zero, zero_add,
          Nat.sub_add_cancel hbig]
        ring
      · have hndvd : ¬ p ^ j ∣ n := by
          rintro ⟨c, hc⟩
          rcases c with _ | _ | c
          · exact h0 (by simpa using hc)
          · exact hNn (by simpa using hc)
          · apply hbig
            rw [hc]
            nlinarith
        have hor : ¬ (n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n) := by omega
        rw [if_neg h0, if_neg hor, if_neg hNn, if_neg hbig, map_neg, hw n h0 hndvd, mul_zero,
          sub_zero, add_zero]
        ring

/-- **Fontaine, Lemme 4.3.1** (power-series form): for `a ∈ S` nonzero, `a · u ∉ S`, where
`u = −Σ_{n ≥ 1} β^n/n` (`logNeg`). -/
theorem notMem_mul_log [Fact p.Prime] {β : P} (hβI : β ∈ I) (ξ : A) {pinv : P}
    (hpβ : (p : P) * β = algebraMap A P ξ) (hpinv : (p : P) * pinv = 1)
    (hξI : algebraMap A P ξ ∈ I) (inv : ℕ → P)
    (hinv : ∀ n : ℕ, n ≠ 0 → (n : P) * inv n = 1)
    (hint : ∀ n : ℕ, n ≠ 0 → ∃ w : A, algebraMap A P w * (n : P) = (p : P) ^ padicValNat p n)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (hsepA : ∀ (m : ℕ) (w : A), (∀ k : ℕ, ∃ a b : A, w = (p : A) ^ k * a + ξ ^ m * b) →
      w ∈ Ideal.span {ξ ^ m})
    (hreg : ∀ x : AdicCompletion I P,
      algebraMap P (AdicCompletion I P) (algebraMap A P ξ) * x = 0 → x = 0)
    (a : AdicCompletion I P) (ha : a ∈ SubS A I hβI) (ha0 : a ≠ 0) :
    a * psEval I hβI (logNeg inv) ∉ SubS A I hβI := by
  classical
  intro hb
  have hp := (Fact.out : p.Prime)
  obtain ⟨b, hbdef⟩ : ∃ b : AdicCompletion I P, b = algebraMap P (AdicCompletion I P) β := ⟨_, rfl⟩
  obtain ⟨π, hπdef⟩ : ∃ π : AdicCompletion I P, π = algebraMap P (AdicCompletion I P) pinv :=
    ⟨_, rfl⟩
  have hpp : (p : AdicCompletion I P) * π = 1 := by
    rw [hπdef, ← map_natCast (algebraMap P (AdicCompletion I P)), ← map_mul, hpinv, map_one]
  have hbreg : ∀ x : AdicCompletion I P, b * x = 0 → x = 0 := by
    intro x hx
    have h1 : algebraMap P (AdicCompletion I P) (algebraMap A P ξ) * (π * x) = 0 := by
      rw [← hpβ, map_mul, map_natCast, ← hbdef]
      have e : (p : AdicCompletion I P) * b * (π * x) = π * (p : AdicCompletion I P) * (b * x) := by
        ring
      rw [e, hx, mul_zero]
    have h2 := hreg _ h1
    calc x = (p : AdicCompletion I P) * π * x := by rw [hpp, one_mul]
      _ = (p : AdicCompletion I P) * (π * x) := by ring
      _ = 0 := by rw [h2, mul_zero]
  have hbpow : ∀ (k : ℕ) (x y : AdicCompletion I P), b ^ k * x = b ^ k * y → x = y := by
    intro k
    induction k with
    | zero => intro x y h; simpa using h
    | succ k ih =>
      intro x y h
      apply ih
      have h' : b * (b ^ k * x - b ^ k * y) = 0 := by
        have e : b * (b ^ k * x - b ^ k * y) = b ^ (k + 1) * x - b ^ (k + 1) * y := by ring
        rw [e, h, sub_self]
      exact sub_eq_zero.mp (hbreg _ h')
  have hbS : b ∈ SubS A I hβI := by
    refine (mem_subS A I hβI b).mpr ⟨PowerSeries.X, ?_⟩
    rw [PowerSeries.map_X, psEval_X I hβI, hbdef]
  have hpS : ∀ k : ℕ, ((p : AdicCompletion I P) ^ k) ∈ SubS A I hβI := fun k =>
    Subring.pow_mem _ (natCast_mem _ p) k
  -- Step 1: `a = p^r a'` with `a' ∉ p S`.
  have hex : ∃ k : ℕ, ¬ ∃ y ∈ SubS A I hβI, a = (p : AdicCompletion I P) ^ k * y := by
    by_contra hc
    push_neg at hc
    exact ha0 (s_sep A I p hβI ξ hpβ hpinv hξI hξpow hsepA a hc)
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this ⟨a, ha, by rw [pow_zero, one_mul]⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.find hex = r + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hra : ∃ y ∈ SubS A I hβI, a = (p : AdicCompletion I P) ^ r * y := by
    have := Nat.find_min hex (show r < Nat.find hex by omega)
    push_neg at this
    exact this
  obtain ⟨a', ha'S, haa'⟩ := hra
  have ha'p : ¬ ∃ y ∈ SubS A I hβI, a' = (p : AdicCompletion I P) * y := by
    rintro ⟨y, hy, hy'⟩
    have := Nat.find_spec hex
    rw [hr] at this
    exact this ⟨y, hy, by rw [haa', hy']; ring⟩
  -- Step 2: the first coefficient outside `(p, ξ)`.
  obtain ⟨f, hf⟩ := (mem_subS A I hβI a').mp ha'S
  have hcex : ∃ n, PowerSeries.coeff n f ∉ Ideal.span {(p : A), ξ} := by
    by_contra hc
    push_neg at hc
    obtain ⟨y, hy, hy'⟩ := mem_pS_of_coeff A I p hβI ξ hpβ f hc
    exact ha'p ⟨y, hy, by rw [← hf, hy']⟩
  have hci : PowerSeries.coeff (Nat.find hcex) f ∉ Ideal.span {(p : A), ξ} := Nat.find_spec hcex
  have hlow : ∀ n < Nat.find hcex, PowerSeries.coeff n f ∈ Ideal.span {(p : A), ξ} := by
    intro n hn
    have := Nat.find_min hcex hn
    push_neg at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, i = Nat.find hcex := ⟨_, rfl⟩
  rw [← hi] at hci hlow
  obtain ⟨s, hsS, hsdec⟩ := decomp_min A I p hβI ξ hpβ f i hlow
  rw [← hbdef, hf] at hsdec
  -- `h = C h₀ + X h'`
  obtain ⟨H, hHdef⟩ : ∃ H : AdicCompletion I P, H = psEval I hβI (PowerSeries.map (algebraMap A P)
      (PowerSeries.mk fun k => PowerSeries.coeff (k + i) f)) := ⟨_, rfl⟩
  obtain ⟨h', hh'def⟩ : ∃ h' : AdicCompletion I P, h' = psEval I hβI (PowerSeries.map (algebraMap A P)
      (PowerSeries.mk fun k => PowerSeries.coeff (k + 1 + i) f)) := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0 : AdicCompletion I P,
      c0 = algebraMap P (AdicCompletion I P) (algebraMap A P (PowerSeries.coeff i f)) := ⟨_, rfl⟩
  have hHdec : H = c0 + b * h' := by
    have hd : (PowerSeries.mk fun k => PowerSeries.coeff (k + i) f) =
        PowerSeries.C (PowerSeries.coeff i f) +
          PowerSeries.X * PowerSeries.mk fun k => PowerSeries.coeff (k + 1 + i) f := by
      ext n
      rcases n with _ | n
      · rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, if_pos rfl,
          PowerSeries.coeff_zero_X_mul, add_zero, zero_add]
      · rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), zero_add,
          PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    rw [hHdef, hd, map_add, map_add, PowerSeries.map_C, psEval_C I hβI, map_mul, map_mul,
      PowerSeries.map_X, psEval_X I hβI, hc0def, hbdef, hh'def]
  rw [← hHdef] at hsdec
  -- Step 3: the splitting of `u` at `N = p^j`.
  obtain ⟨j, hjdef⟩ : ∃ j, j = i + r + 1 := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by omega
  have hiN : i < p ^ j := lt_of_lt_of_le (show i < j by omega)
    (le_of_lt (lt_pow_of_two_le hp.two_le j))
  obtain ⟨q, T, hqT⟩ := log_split A p hpinv inv hinv hint j hj1
  obtain ⟨T', hT'def⟩ : ∃ T' : AdicCompletion I P, T' = psEval I hβI T := ⟨_, rfl⟩
  obtain ⟨Q', hQ'def⟩ : ∃ Q' : AdicCompletion I P,
      Q' = psEval I hβI (PowerSeries.map (algebraMap A P) q) := ⟨_, rfl⟩
  have hU : (p : AdicCompletion I P) ^ (j - 1) * psEval I hβI (logNeg inv) =
      Q' - π * b ^ (p ^ j) + b ^ (2 * p ^ j) * T' := by
    have := congrArg (psEval I hβI) hqT
    rw [map_mul, psEval_C I hβI, map_pow, map_natCast, map_add, map_sub, map_mul, map_mul,
      psEval_C I hβI, map_pow, map_pow, psEval_X I hβI] at this
    rw [this, hQ'def, hπdef, hbdef, hT'def]
  have hle : r ≤ j - 1 := by omega
  have hpr : (p : AdicCompletion I P) ^ (j - 1) =
      (p : AdicCompletion I P) ^ (j - 1 - r) * (p : AdicCompletion I P) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hmem1 : (p : AdicCompletion I P) ^ (j - 1) * (a' * psEval I hβI (logNeg inv)) ∈
      SubS A I hβI := by
    have e : (p : AdicCompletion I P) ^ (j - 1) * (a' * psEval I hβI (logNeg inv)) =
        (p : AdicCompletion I P) ^ (j - 1 - r) * (a * psEval I hβI (logNeg inv)) := by
      rw [hpr, haa']; ring
    rw [e]
    exact Subring.mul_mem _ (hpS _) hb
  obtain ⟨s1, hs1def⟩ : ∃ s1 : AdicCompletion I P, s1 = a' * Q' -
      (p : AdicCompletion I P) ^ (j - 1) * (a' * psEval I hβI (logNeg inv)) := ⟨_, rfl⟩
  have hs1S : s1 ∈ SubS A I hβI := by
    rw [hs1def, hQ'def]
    exact Subring.sub_mem _ (Subring.mul_mem _ ha'S (psEval_map_mem A I hβI q)) hmem1
  have hkey : a' * π * b ^ (p ^ j) = s1 + b ^ (2 * p ^ j) * (a' * T') := by
    have e : (p : AdicCompletion I P) ^ (j - 1) * (a' * psEval I hβI (logNeg inv)) =
        a' * ((p : AdicCompletion I P) ^ (j - 1) * psEval I hβI (logNeg inv)) := by ring
    rw [hs1def, e, hU]
    ring
  -- `σ = β^{i+N} Z` with `σ ∈ S`
  have hσS : s1 - s * b ^ (p ^ j) ∈ SubS A I hβI :=
    Subring.sub_mem _ hs1S (Subring.mul_mem _ hsS (Subring.pow_mem _ hbS _))
  have e2N : b ^ (2 * p ^ j) = b ^ (i + p ^ j) * b ^ (p ^ j - i) := by
    rw [← pow_add]
    congr 1
    omega
  have eiN : b ^ (i + p ^ j) = b ^ i * b ^ (p ^ j) := pow_add b i (p ^ j)
  have hσZ : s1 - s * b ^ (p ^ j) =
      b ^ (i + p ^ j) * (π * c0 - b ^ (p ^ j - i) * (a' * T') + b * (π * h')) := by
    have ha'dec : a' = (p : AdicCompletion I P) * s + b ^ i * H := hsdec
    linear_combination (-1 : AdicCompletion I P) * hkey + (π * b ^ (p ^ j)) * ha'dec +
      (s * b ^ (p ^ j)) * hpp + (b ^ (i + p ^ j) * π) * hHdec - (π * H) * eiN - (a' * T') * e2N
  -- `σ ∈ β^{i+N} S`, then cancel `β^{i+N}`.
  obtain ⟨g0, hg0⟩ := (mem_subS A I hβI _).mp hσS
  have hev0 : AdicCompletion.evalₐ I (i + p ^ j)
      (psEval I hβI (PowerSeries.map (algebraMap A P) g0)) = 0 := by
    rw [hg0, hσZ, map_mul, map_pow, hbdef, evalₐ_algebraMap I, ← map_pow,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.pow_mem_pow hβI _), zero_mul]
  obtain ⟨g, hg⟩ := s_fil A I p hβI ξ hpβ hpinv hξpow g0 (i + p ^ j) hev0
  rw [hg0, hσZ, ← hbdef] at hg
  have hZ := hbpow _ _ _ hg
  -- reduce modulo `I`
  have hZ1 := congrArg (AdicCompletion.evalₐ I 1) hZ
  have hβ1 : AdicCompletion.evalₐ I 1 b = 0 := by
    rw [hbdef, evalₐ_algebraMap I, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hβI
  have hNi0 : p ^ j - i ≠ 0 := by omega
  have htr : AdicCompletion.evalₐ I 1 (psEval I hβI (PowerSeries.map (algebraMap A P) g)) =
      Ideal.Quotient.mk (I ^ 1) (algebraMap A P (PowerSeries.coeff 0 g)) := by
    rw [evalₐ_psEval, Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.sum_range_one, pow_zero,
      mul_one, RingHom.id_apply, PowerSeries.coeff_map]
  simp only [map_add, map_sub, map_mul, map_pow, hβ1, zero_pow hNi0, zero_mul, mul_zero, sub_zero,
    add_zero, htr] at hZ1
  rw [hπdef, hc0def, evalₐ_algebraMap I, evalₐ_algebraMap I, ← map_mul, Ideal.Quotient.eq,
    pow_one] at hZ1
  have hmem : algebraMap A P (PowerSeries.coeff i f - (p : A) * PowerSeries.coeff 0 g) ∈ I ^ 1 := by
    have e : algebraMap A P (PowerSeries.coeff i f - (p : A) * PowerSeries.coeff 0 g) =
        (p : P) * (pinv * algebraMap A P (PowerSeries.coeff i f) -
          algebraMap A P (PowerSeries.coeff 0 g)) := by
      rw [map_sub, map_mul, map_natCast]
      linear_combination (-(algebraMap A P (PowerSeries.coeff i f))) * hpinv
    rw [e, pow_one]
    exact Ideal.mul_mem_left _ _ hZ1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hξpow 1 _ hmem)
  apply hci
  refine Ideal.mem_span_pair.mpr ⟨PowerSeries.coeff 0 g, d, ?_⟩
  rw [pow_one] at hd
  linear_combination hd

end Core

end FontaineLogCore
