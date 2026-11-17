import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Shell

/-!
# Lane RC12-odd: the operators `U_p − η(p) V_p` on an abstract coefficient function (App F)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules` (tex 9491–9617):
`B_U = 2^{−n_U} ∏_{p∈U}(U_p − η(p)V_p) g`, where `U_p(∑ a(n)qⁿ) = ∑ a(pn)qⁿ` and `V_p g(τ) = g(pτ)`,
together with the all-index recurrence (O.6) of Proposition `ex:app-theta-form` (tex 9083–9098):
`a(p²n) = {η(p)a_p − ψ(p)(−n/p)} a(n) − p η(p)² a(n/p²)`, nonintegral indices read as zero.

We work with an abstract coefficient function `a : ℕ → R` over a commutative ring `R` (the
coefficient ring `𝒪`, or `𝒪/2^M𝒪` for an odd stage). Writing `ψ(p) = η(p) ε_p` with
`ε_p = (ψ/η)(p) ∈ {±1}` (for the odd source `ψ/η = χ_{−1}`, (O.5)), (O.6) at `p` is `RecAt`.

* `rec_even`, `rec_odd`: the shell formulas `a(p^{2s} n') = η^s b_s a(n')` (`κ = ε (−n'/p)`) and
  `a(p^{2s+1} n') = η^s b⁰_s a(pn')` (`κ = 0`) for `p ∤ n'` ("Remove the phase `η(p)^s` in (O.6)",
  tex 9562–9566).
* `Top_even`, `Top_odd`: the coefficient of `(U_p − η(p)V_p) g` at `p^k n'` is
  `η^s (b⁰_s − b⁰_{s−1}) a(pn')` (`k = 2s`, `p ∉ J`) or `η^{s+1}(b_{s+1} − b_s) a(n')` (`k = 2s+1`,
  `p ∈ J`) (tex 9567–9569).
* `RecAt.top`: after `U_p − η(p)V_p` the recurrence at another prime `q` holds with `ψ` replaced by
  `ψ (p/·)` ("`V_p g` has level `4Ap` and character `ψ(p/·)`", tex 9511–9512, 9543–9546).
* `Top_comm`: the operators at distinct primes commute, so `B_U` depends only on the set `U`.

All statements are PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

variable {R : Type*} [CommRing R]

/-- The coefficient at the index `n/d`, read as zero when `d ∤ n` (nonintegral index). -/
def divCoeff (a : ℕ → R) (d n : ℕ) : R := if d ∣ n then a (n / d) else 0

/-- `U_p − η V_p` on Fourier coefficients: `n ↦ a(pn) − η a(n/p)` (tex 9494–9496). -/
def Top (p : ℕ) (η : R) (a : ℕ → R) (n : ℕ) : R := a (p * n) - η * divCoeff a p n

/-- **The recurrence (O.6) at `p`** (tex 9086–9089), with `η = η(p)`, `ψ(p) = η ε`, and `a_p`:
`a(p²n) = η (a_p − ε (−n/p)) a(n) − p η² a(n/p²)` at every index `n`. -/
def RecAt (p : ℕ) [Fact p.Prime] (η : R) (ε ap : ℤ) (a : ℕ → R) : Prop :=
  ∀ n : ℕ, a (p ^ 2 * n) =
    η * ((ap - ε * legendreSym p (-(n : ℤ)) : ℤ) : R) * a n - (p : R) * η ^ 2 * divCoeff a (p ^ 2) n

theorem divCoeff_mul_left (a : ℕ → R) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    divCoeff a d (d * n) = a n := by
  simp [divCoeff, Nat.mul_div_cancel_left n hd]

theorem divCoeff_of_not_dvd (a : ℕ → R) {d n : ℕ} (h : ¬ d ∣ n) : divCoeff a d n = 0 := by
  simp [divCoeff, h]

theorem legendreSym_neg_eq_zero_of_dvd {p : ℕ} [Fact p.Prime] {n : ℕ} (h : p ∣ n) :
    legendreSym p (-(n : ℤ)) = 0 := by
  rw [legendreSym.eq_zero_iff]
  obtain ⟨c, rfl⟩ := h
  simp

variable {p : ℕ} [hp : Fact p.Prime] {η : R} {ε ap : ℤ} {a : ℕ → R}

omit hp in
theorem not_sq_dvd_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : ¬ p ^ 2 ∣ n :=
  fun h2 => h (dvd_trans (dvd_pow_self p two_ne_zero) h2)

theorem not_sq_dvd_mul_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : ¬ p ^ 2 ∣ p * n := by
  rintro ⟨c, hc⟩
  apply h
  refine ⟨c, ?_⟩
  have hp0 : 0 < p := hp.out.pos
  rw [pow_two, mul_assoc] at hc
  exact Nat.eq_of_mul_eq_mul_left hp0 hc

/-- **PROVED (tex 9562–9566).** Even shells: for `p ∤ n'`,
`a(p^{2s} n') = η^s b_s(a_p, p, κ) a(n')` with `κ = ε (−n'/p)`. -/
theorem rec_even (hrec : RecAt p η ε ap a) {n' : ℕ} (hn' : ¬ p ∣ n') (s : ℕ) :
    a (p ^ (2 * s) * n') =
      η ^ s * (shell ap p (ε * legendreSym p (-(n' : ℤ))) s : R) * a n' := by
  have hp0 : 0 < p := hp.out.pos
  set κ := ε * legendreSym p (-(n' : ℤ)) with hκ
  have key : ∀ t, a (p ^ (2 * t) * n') = η ^ t * (shell ap p κ t : R) * a n' ∧
      a (p ^ (2 * (t + 1)) * n') = η ^ (t + 1) * (shell ap p κ (t + 1) : R) * a n' := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp, ?_⟩
      have := hrec n'
      rw [divCoeff_of_not_dvd a (not_sq_dvd_of_not_dvd hn')] at this
      simp only [zero_add, mul_one, pow_one, shell_one]
      rw [this, hκ]; push_cast; ring
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      have := hrec (p ^ (2 * (t + 1)) * n')
      have hidx : p ^ 2 * (p ^ (2 * (t + 1)) * n') = p ^ (2 * (t + 1 + 1)) * n' := by ring
      rw [hidx] at this
      rw [this, legendreSym_neg_eq_zero_of_dvd (dvd_mul_of_dvd_left
        (dvd_pow_self p (by omega)) _)]
      have hdc : divCoeff a (p ^ 2) (p ^ (2 * (t + 1)) * n') = a (p ^ (2 * t) * n') := by
        rw [show p ^ (2 * (t + 1)) * n' = p ^ 2 * (p ^ (2 * t) * n') by ring,
          divCoeff_mul_left a (by positivity)]
      rw [hdc, ih.1, ih.2, show t + 1 + 1 = t + 2 by ring, shell_succ_succ]
      push_cast; ring
  exact (key s).1

/-- **PROVED (tex 9562–9566, `κ = 0`).** Odd shells: for `p ∤ n'`,
`a(p^{2s+1} n') = η^s b_s(a_p, p, 0) a(p n')`. -/
theorem rec_odd (hrec : RecAt p η ε ap a) {n' : ℕ} (hn' : ¬ p ∣ n') (s : ℕ) :
    a (p ^ (2 * s + 1) * n') = η ^ s * (shell ap p 0 s : R) * a (p * n') := by
  have hp0 : 0 < p := hp.out.pos
  have key : ∀ t, a (p ^ (2 * t + 1) * n') = η ^ t * (shell ap p 0 t : R) * a (p * n') ∧
      a (p ^ (2 * (t + 1) + 1) * n') = η ^ (t + 1) * (shell ap p 0 (t + 1) : R) * a (p * n') := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp, ?_⟩
      have := hrec (p * n')
      rw [divCoeff_of_not_dvd a (not_sq_dvd_mul_of_not_dvd hn'),
        legendreSym_neg_eq_zero_of_dvd (dvd_mul_right p n')] at this
      simp only [zero_add, mul_one, pow_one, shell_one]
      rw [show p ^ (2 * 1 + 1) * n' = p ^ 2 * (p * n') by ring, this]; push_cast; ring
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      have := hrec (p ^ (2 * (t + 1) + 1) * n')
      have hidx : p ^ 2 * (p ^ (2 * (t + 1) + 1) * n') = p ^ (2 * (t + 1 + 1) + 1) * n' := by
        ring
      rw [hidx] at this
      rw [this, legendreSym_neg_eq_zero_of_dvd (dvd_mul_of_dvd_left
        (dvd_pow_self p (by omega)) _)]
      have hdc : divCoeff a (p ^ 2) (p ^ (2 * (t + 1) + 1) * n') = a (p ^ (2 * t + 1) * n') := by
        rw [show p ^ (2 * (t + 1) + 1) * n' = p ^ 2 * (p ^ (2 * t + 1) * n') by ring,
          divCoeff_mul_left a (by positivity)]
      rw [hdc, ih.1, ih.2, show t + 1 + 1 = t + 2 by ring, shell_succ_succ]
      push_cast; ring
  exact (key s).1

/-- **PROVED (tex 9567–9568).** For `p ∉ J` (even exponent `2s` of `p` in the index):
the coefficient of `(U_p − η V_p) g` is `η^s (b⁰_s − b⁰_{s−1}) a(pn')`. -/
theorem Top_even (hrec : RecAt p η ε ap a) {n' : ℕ} (hn' : ¬ p ∣ n') (s : ℕ) :
    Top p η a (p ^ (2 * s) * n') =
      η ^ s * ((shell ap p 0 s - shellPrev ap p 0 s : ℤ) : R) * a (p * n') := by
  have hp0 : 0 < p := hp.out.pos
  cases s with
  | zero =>
    simp [Top, divCoeff_of_not_dvd a hn']
  | succ s =>
    simp only [Top]
    rw [show p * (p ^ (2 * (s + 1)) * n') = p ^ (2 * (s + 1) + 1) * n' by ring,
      show p ^ (2 * (s + 1)) * n' = p * (p ^ (2 * s + 1) * n') by ring,
      divCoeff_mul_left a hp0, rec_odd hrec hn', rec_odd hrec hn', shellPrev_succ]
    push_cast; ring

/-- **PROVED (tex 9569).** For `p ∈ J` (odd exponent `2s+1`): the coefficient of
`(U_p − η V_p) g` is `η^{s+1} (b_{s+1} − b_s) a(n')`, `κ = ε (−n'/p)`. -/
theorem Top_odd (hrec : RecAt p η ε ap a) {n' : ℕ} (hn' : ¬ p ∣ n') (s : ℕ) :
    Top p η a (p ^ (2 * s + 1) * n') =
      η ^ (s + 1) * ((shellDiff ap p (ε * legendreSym p (-(n' : ℤ))) s : ℤ) : R) * a n' := by
  have hp0 : 0 < p := hp.out.pos
  simp only [Top]
  rw [show p * (p ^ (2 * s + 1) * n') = p ^ (2 * (s + 1)) * n' by ring,
    show p ^ (2 * s + 1) * n' = p * (p ^ (2 * s) * n') by ring,
    divCoeff_mul_left a hp0, rec_even hrec hn', rec_even hrec hn', shellDiff]
  push_cast; ring

omit hp in
/-- For `p ∤ n`, `(U_p − η V_p)` reads the coefficient at `pn` (tex 9681–9686). -/
theorem Top_of_not_dvd (a : ℕ → R) {n : ℕ} (hn : ¬ p ∣ n) : Top p η a n = a (p * n) := by
  simp [Top, divCoeff_of_not_dvd a hn]

/-! ### Coprime index shifts, the twisted recurrence and commutation -/

omit hp in
theorem divCoeff_mul_coprime (a : ℕ → R) {d e n : ℕ} (hde : Nat.Coprime d e) :
    divCoeff a d (e * n) = divCoeff (fun m => a (e * m)) d n := by
  by_cases h : d ∣ n
  · obtain ⟨c, rfl⟩ := h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [divCoeff]
    rw [show e * (d * c) = d * (e * c) by ring, divCoeff_mul_left a hd,
      divCoeff_mul_left _ hd]
  · rw [divCoeff_of_not_dvd _ h, divCoeff_of_not_dvd]
    exact fun h' => h ((Nat.Coprime.dvd_mul_left hde).mp h')

omit hp in
theorem divCoeff_divCoeff_comm (a : ℕ → R) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hde : Nat.Coprime d e) (n : ℕ) :
    divCoeff (divCoeff a d) e n = divCoeff (divCoeff a e) d n := by
  by_cases h : d * e ∣ n
  · obtain ⟨c, rfl⟩ := h
    rw [show d * e * c = e * (d * c) by ring, divCoeff_mul_left _ he, divCoeff_mul_left a hd,
      show e * (d * c) = d * (e * c) by ring, divCoeff_mul_left _ hd, divCoeff_mul_left a he]
  · have key : ∀ (x y : ℕ), 0 < x → 0 < y → ¬ x * y ∣ n → Nat.Coprime x y →
        divCoeff (divCoeff a x) y n = 0 := by
      intro x y hx hy hxy hc
      by_cases hyn : y ∣ n
      · obtain ⟨c, rfl⟩ := hyn
        rw [divCoeff_mul_left _ hy, divCoeff_of_not_dvd]
        intro hxc
        apply hxy
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc (dvd_mul_of_dvd_right hxc y)
          (dvd_mul_right y c)
      · exact divCoeff_of_not_dvd _ hyn
    rw [key d e hd he h hde, key e d he hd (by rwa [mul_comm]) hde.symm]

omit hp in
/-- `V_p` commutes with reading at `n/d` for `d` prime to `p`. -/
theorem divCoeff_Top (a : ℕ → R) {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (hdq : Nat.Coprime d q)
    (η : R) (n : ℕ) : divCoeff (Top q η a) d n = Top q η (divCoeff a d) n := by
  simp only [Top]
  rw [divCoeff_mul_coprime a hdq, divCoeff_divCoeff_comm a hd hq hdq]
  by_cases h : d ∣ n
  · obtain ⟨c, rfl⟩ := h
    simp only [divCoeff_mul_left _ hd, Top]
  · simp only [divCoeff_of_not_dvd _ h, mul_zero, sub_zero]

/-- **PROVED (tex 9497–9512, 9543–9546).** After `U_p − η(p) V_p`, the recurrence (O.6) at another
prime `q` holds with the same `η(q)` and with `ψ` replaced by `ψ (p/·)`, i.e. `ε_q ↦ ε_q (p/q)`. -/
theorem RecAt.top {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q) {ηq : R} {εq aq : ℤ}
    (hrec : RecAt q ηq εq aq a) (ηp : R) :
    RecAt q ηq (εq * legendreSym q p) aq (Top p ηp a) := by
  intro n
  have hq0 : 0 < q := hq.out.pos
  have hp0 : 0 < p := hp.out.pos
  have hcop : Nat.Coprime p (q ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp.out hq.out).mpr hpq)
  have hleg2 : legendreSym q (p : ℤ) ^ 2 = 1 := by
    apply legendreSym.sq_one
    intro h0
    have : (q : ℤ) ∣ (p : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h0
    have := Int.natCast_dvd_natCast.mp this
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp this).symm
  have hmul : ∀ m : ℕ, legendreSym q (-((p * m : ℕ) : ℤ)) =
      legendreSym q p * legendreSym q (-(m : ℤ)) := by
    intro m; rw [← legendreSym.mul]; congr 1; push_cast; ring
  have hΦ := fun m => hrec m
  simp only [Top]
  rw [show p * (q ^ 2 * n) = q ^ 2 * (p * n) by ring, hrec (p * n), hmul n,
    divCoeff_mul_coprime a hcop, divCoeff_Top a (by positivity) hp0 hcop.symm]
  simp only [Top]
  by_cases hpn : p ∣ n
  · obtain ⟨n₁, rfl⟩ := hpn
    simp only [divCoeff_mul_left _ hp0]
    rw [hrec n₁]
    have hrel : legendreSym q (-(n₁ : ℤ)) =
        legendreSym q p * legendreSym q (-((p * n₁ : ℕ) : ℤ)) := by
      rw [hmul n₁, ← mul_assoc, ← pow_two, hleg2, one_mul]
    rw [hrel]
    push_cast
    ring
  · simp only [divCoeff_of_not_dvd _ hpn]
    push_cast
    ring

omit hp in
/-- **PROVED.** The operators at coprime indices commute, so `∏_{p∈U}(U_p − η(p)V_p)` and hence
`B_U` depend only on the set `U` (tex 9494). -/
theorem Top_comm (a : ℕ → R) {p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hpq : Nat.Coprime p q)
    (ηp ηq : R) : Top p ηp (Top q ηq a) = Top q ηq (Top p ηp a) := by
  funext n
  simp only [Top]
  rw [divCoeff_Top a hp0 hq0 hpq, divCoeff_Top a hq0 hp0 hpq.symm]
  simp only [Top]
  rw [divCoeff_mul_coprime a hpq.symm, divCoeff_mul_coprime a hpq,
    divCoeff_divCoeff_comm a hp0 hq0 hpq]
  rw [show q * (p * n) = p * (q * n) by ring]
  ring

end ZInQ.Manuscript.RC.Odd
