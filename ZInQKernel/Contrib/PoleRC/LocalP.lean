import ZInQKernel.Contrib.PoleRC.Count
import ZInQKernel.RouteK.Selmer.Good

/-!
# The local images of the Kummer map of `E_ℓ`: the "only if" halves

`p`-adic proofs of the necessity directions of `LocalGood`, `LocalThree` and `LocalBad`
(Route K's `Selmer/Good.lean` is the model), and the square-class invariance of `LocM`.
-/

namespace ZInQ.Manuscript.PoleRC

open ZInQ.RouteK.Selmer

section Field

variable {K : Type*} [Field K]

theorem sqEq_of_isSquare_div {u a : K} (hu : u ≠ 0) (ha : a ≠ 0) (h : IsSquare (u / a)) :
    SqEq u a := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero, div_eq_zero_iff] at hr; tauto
  exact ⟨r, hr0, by rw [sq, ← hr]; field_simp⟩

/-- **The torsion alternative for `LocM`**: a witness `x` is one of the roots `−3ℓ, ℓ, 0` (and then
`(a, b)` is a torsion class) or `x ≡ ab`, `x + 3ℓ ≡ a`, `x − ℓ ≡ b`. -/
theorem locM_torsion [CharZero K] {ℓ a b x : K} (hℓ : ℓ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : IsSquare ((x + 3 * ℓ) / a)) (h₂ : IsSquare ((x - ℓ) / b))
    (h₃ : IsSquare (x / (a * b))) :
    (x = -3 * ℓ ∧ SqEq b (-ℓ) ∧ SqEq (a * b) (-3 * ℓ)) ∨ (x = ℓ ∧ SqEq a ℓ ∧ SqEq (a * b) ℓ) ∨
      (x = 0 ∧ SqEq a (3 * ℓ) ∧ SqEq b (-ℓ)) ∨
      (x ≠ 0 ∧ x - ℓ ≠ 0 ∧ x + 3 * ℓ ≠ 0 ∧ SqEq (x + 3 * ℓ) a ∧ SqEq (x - ℓ) b ∧
        SqEq x (a * b)) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hsq4 : ∀ (u : K), SqEq (4 * u) u := fun u => ⟨2, h2, by ring⟩
  by_cases hx3 : x = -3 * ℓ
  · left
    subst hx3
    have hm : -3 * ℓ - ℓ ≠ 0 := by
      rw [show -3 * ℓ - ℓ = -4 * ℓ by ring]; exact mul_ne_zero (by norm_num) hℓ
    have h3 : -3 * ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓ
    refine ⟨rfl, ?_, (sqEq_of_isSquare_div h3 hab h₃).symm⟩
    exact (sqEq_of_isSquare_div hm hb h₂).symm.trans
      (by rw [show -3 * ℓ - ℓ = 4 * (-ℓ) by ring]; exact hsq4 _)
  by_cases hx1 : x = ℓ
  · right; left
    subst hx1
    have h4 : x + 3 * x ≠ 0 := by rw [show x + 3 * x = 4 * x by ring]; exact mul_ne_zero (by norm_num) hℓ
    refine ⟨rfl, ?_, (sqEq_of_isSquare_div hℓ hab h₃).symm⟩
    exact (sqEq_of_isSquare_div h4 ha h₁).symm.trans
      (by rw [show x + 3 * x = 4 * x by ring]; exact hsq4 _)
  by_cases hx0 : x = 0
  · right; right; left
    subst hx0
    refine ⟨rfl, ?_, ?_⟩
    · have h3 : (0 : K) + 3 * ℓ ≠ 0 := by rw [zero_add]; exact mul_ne_zero (by norm_num) hℓ
      have := (sqEq_of_isSquare_div h3 ha h₁).symm
      rwa [zero_add] at this
    · have hm : (0 : K) - ℓ ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr hℓ
      have := (sqEq_of_isSquare_div hm hb h₂).symm
      rwa [zero_sub] at this
  right; right; right
  have hxa : x + 3 * ℓ ≠ 0 := fun h => hx3 (by linear_combination h)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  exact ⟨hx0, hxb, hxa, sqEq_of_isSquare_div hxa ha h₁, sqEq_of_isSquare_div hxb hb h₂,
    sqEq_of_isSquare_div hx0 hab h₃⟩

end Field

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_norm_three (hp3 : p ≠ 3) : ‖(3 : ℚ_[p])‖ = 1 := by
  have := padic_norm_intCast_eq_one (p := p) (c := 3) (by
    intro h
    have : p ∣ 3 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this))
  simpa using this

theorem padic_norm_mul_one {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x * y‖ = 1 := by
  rw [norm_mul, hx, hy, one_mul]

/-- `LocM` at a good prime puts `a` and `b` in the square classes of units. -/
theorem locM_good_units (hp2 : p ≠ 2) (hp3 : p ≠ 3) {L A B : ℚ_[p]} (hL : ‖L‖ = 1)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (h : LocM ℚ_[p] L A B) :
    ∃ u w : ℚ_[p], ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ SqEq A u ∧ SqEq B w := by
  have hL0 : L ≠ 0 := by intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  have hn3 := padic_norm_three (p := p) hp3
  have hn4 : ‖(4 : ℚ_[p])‖ = 1 := by
    rw [show (4 : ℚ_[p]) = 2 * 2 by norm_num, norm_mul, padic_norm_two hp2, one_mul]
  have hnL : ‖-L‖ = 1 := by rw [norm_neg, hL]
  have hn3L : ‖3 * L‖ = 1 := padic_norm_mul_one hn3 hL
  have hn4L : ‖4 * L‖ = 1 := padic_norm_mul_one hn4 hL
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact ⟨1, 1, norm_one, norm_one, (sqEq_iff_isSquare_mul hA0 one_ne_zero).mpr (by simpa),
      (sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa)⟩
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', hab'⟩ | ⟨-, ha', hab'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · have ha' : SqEq A (-3 * L * -L) := sqEq_of_mul_sqEq hab' hb' (neg_ne_zero.mpr hL0)
    exact ⟨_, _, by rw [show -3 * L * -L = 3 * L * L by ring, norm_mul, hn3L, hL, one_mul],
      hnL, ha', hb'⟩
  · have hba : SqEq (B * A) L := by rw [mul_comm]; exact hab'
    exact ⟨_, _, hL, padic_norm_mul_one hL hL, ha', sqEq_of_mul_sqEq hba ha' hL0⟩
  · exact ⟨_, _, hn3L, hnL, ha', hb'⟩
  rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
  · have e₂ : SqEq (x - L) (-L) := by
      rw [show x - L = -L + x by ring]; exact sqEq_add_of_norm_lt hp2 (by rwa [hnL])
    have e₃ : SqEq (x + 3 * L) (3 * L) := by
      rw [add_comm]; exact sqEq_add_of_norm_lt hp2 (by rwa [hn3L])
    exact ⟨_, _, hn3L, hnL, hxa'.symm.trans e₃, hxb'.symm.trans e₂⟩
  · have hle : ∀ c : ℚ_[p], ‖c‖ = 1 → ‖x + c‖ ≤ 1 := fun c hc =>
      (Padic.nonarchimedean _ _).trans (by rw [heq, hc, max_self])
    by_cases hm : ‖x - L‖ < 1
    · have hp1 : ‖x + 3 * L‖ = 1 := by
        refine le_antisymm (hle _ hn3L) (not_lt.mp fun hlt' => ?_)
        have := Padic.nonarchimedean (x + 3 * L) (-(x - L))
        rw [show x + 3 * L + -(x - L) = 4 * L by ring, hn4L, norm_neg] at this
        exact absurd this (not_le.mpr (max_lt hlt' hm))
      have hba : SqEq (B * A) x := by rw [mul_comm]; exact hxab.symm
      exact ⟨_, _, hp1, padic_norm_mul_one heq hp1, hxa'.symm,
        sqEq_of_mul_sqEq hba hxa'.symm hxa⟩
    · have hsub : ‖x - L‖ ≤ 1 := by rw [sub_eq_add_neg]; exact hle _ hnL
      have hxL : ‖x - L‖ = 1 := le_antisymm hsub (not_lt.mp hm)
      by_cases hm2 : ‖x + 3 * L‖ < 1
      · exact ⟨_, _, padic_norm_mul_one heq hxL, hxL,
          sqEq_of_mul_sqEq hxab.symm hxb'.symm hxb, hxb'.symm⟩
      · exact ⟨_, _, le_antisymm (hle _ hn3L) (not_lt.mp hm2), hxL, hxa'.symm, hxb'.symm⟩
  · have e₂ : SqEq (x - L) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt hp2 (by rwa [hnL])
    have e₃ : SqEq (x + 3 * L) x := sqEq_add_of_norm_lt hp2 (by rwa [hn3L])
    have hb' : SqEq B x := hxb'.symm.trans e₂
    have hab : SqEq (A * B) x := hxab.symm
    have ha' : SqEq A 1 := by
      have := sqEq_of_mul_sqEq hab hb' hx0
      exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq A (1 * x ^ 2)).of_mul_sq hx0
    exact ⟨1, 1, norm_one, norm_one, ha', hb'.trans ((hxa'.symm.trans e₃).symm.trans ha')⟩

theorem not_dvd_of_sqEq_unit {a : ℤ} (ha : Squarefree a) {u : ℚ_[p]} (hu : ‖u‖ = 1)
    (h : SqEq (a : ℚ_[p]) u) : ¬ (p : ℤ) ∣ a := by
  have e := even_valuation_of_sqEq_unit hu h
  rw [Padic.valuation_intCast] at e
  exact not_dvd_of_squarefree_of_even_padicValInt ha (Int.even_coe_nat _ |>.mp e)

/-- **`LocalGood`, "only if"**: at `p ∤ 6ℓ`, a locally soluble pair of squarefree integers is
prime to `p`. -/
theorem localGood_nec {ℓ : ℕ} {a b : ℤ} (hp6 : ¬ p ∣ 6 * ℓ) (ha : Squarefree a)
    (hb : Squarefree b) (h : LocM ℚ_[p] ℓ a b) : ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hp6 (Dvd.intro (3 * ℓ) (by ring))
  have hp3 : p ≠ 3 := by rintro rfl; exact hp6 (Dvd.intro (2 * ℓ) (by ring))
  have hpl : ¬ (p : ℤ) ∣ (ℓ : ℤ) := fun h' => hp6 (Dvd.dvd.mul_left (by exact_mod_cast h') 6)
  have hL : ‖((ℓ : ℤ) : ℚ_[p])‖ = 1 := padic_norm_intCast_eq_one hpl
  have hA0 : (a : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr ha.ne_zero
  have hB0 : (b : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  obtain ⟨u, w, hu, hw, hAu, hBw⟩ :=
    locM_good_units hp2 hp3 (L := (ℓ : ℚ_[p])) (by simpa using hL) hA0 hB0 h
  exact ⟨not_dvd_of_sqEq_unit ha hu hAu, not_dvd_of_sqEq_unit hb hw hBw⟩

end Padic

section Three

/-- A squarefree integer that is a square in `ℚ_p` (`p` odd) is a nonzero square mod `p`. -/
theorem residue_isSquare_of_padic {p : ℕ} [Fact p.Prime] {b : ℤ} (hb : Squarefree b)
    (h : IsSquare (b : ℚ_[p])) : ¬ (p : ℤ) ∣ b ∧ IsSquare (b : ZMod p) := by
  have hB0 : (b : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  have hnd : ¬ (p : ℤ) ∣ b :=
    not_dvd_of_sqEq_unit hb norm_one ((sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa))
  refine ⟨hnd, ?_⟩
  have hu : ‖(b : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hnd
  obtain ⟨r, -, hr⟩ := exists_padicInt_sq_of_isSquare hu (by rwa [PadicInt.coe_intCast])
  refine ⟨PadicInt.toZMod r, ?_⟩
  have := congrArg PadicInt.toZMod hr
  rwa [map_intCast, map_mul] at this

/-- **`LocalThree`, "only if"**: for `ℓ ≡ 2 (mod 3)`, a locally soluble pair at `3` has
`b ≡ 1 (mod 3)`. -/
theorem localThree_nec {ℓ : ℕ} {a b : ℤ} (h3 : ℓ % 3 = 2) (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[3] ℓ a b) : b % 3 = 1 := by
  set L : ℚ_[3] := (ℓ : ℚ_[3])
  set A : ℚ_[3] := (a : ℚ_[3])
  set B : ℚ_[3] := (b : ℚ_[3])
  have hA0 : A ≠ 0 := Int.cast_ne_zero.mpr ha.ne_zero
  have hB0 : B ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  have hpl : ¬ ((3 : ℕ) : ℤ) ∣ (ℓ : ℤ) := by intro h'; omega
  have hL : ‖L‖ = 1 := by
    have := padic_norm_intCast_eq_one (p := 3) hpl; simpa [L] using this
  have hL0 : L ≠ 0 := by intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  -- `−ℓ` is a `3`-adic square
  have hnL : SqEq (-L) 1 := by
    have hc : ¬ ((3 : ℕ) : ℤ) ∣ (-(ℓ : ℤ)) := by rwa [dvd_neg]
    have hres : IsSquare (((-(ℓ : ℤ)) : ℤ) : ZMod 3) := by
      refine ⟨1, ?_⟩
      rw [mul_one, Int.cast_neg, Int.cast_natCast, ← ZMod.natCast_mod ℓ 3, h3]; decide
    have := isSquare_intCast_of_residue (p := 3) (by norm_num) hc hres
    refine (sqEq_iff_isSquare_mul (neg_ne_zero.mpr hL0) one_ne_zero).mpr ?_
    simpa [L] using this
  have hn3L : ‖3 * L‖ < 1 := by
    rw [norm_mul, hL, mul_one, show (3 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) by norm_num, Padic.norm_p]
    norm_num
  suffices hB1 : SqEq B 1 by
    have hsq : IsSquare B := by
      obtain ⟨s, -, hs⟩ := hB1; exact ⟨s, by rw [hs]; ring⟩
    obtain ⟨hnd, hres⟩ := residue_isSquare_of_padic (p := 3) hb hsq
    have hb0 : (b : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have key : ∀ z : ZMod 3, z ≠ 0 → IsSquare z → z = 1 := by decide
    have h1 := key _ hb0 hres
    have := (ZMod.intCast_eq_intCast_iff' b 1 3).mp (by rw [h1]; simp)
    simpa using this
  rcases h with ⟨-, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact (sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa)
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', -⟩ | ⟨-, ha', hab'⟩ | ⟨-, -, hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · exact hb'.trans hnL
  · have hba : SqEq (B * A) L := by rw [mul_comm]; exact hab'
    exact (sqEq_of_mul_sqEq hba ha' hL0).trans ⟨L, hL0, by ring⟩
  · exact hb'.trans hnL
  by_cases hlt : ‖x‖ < 1
  · have e₂ : SqEq (x - L) (-L) := by
      rw [show x - L = -L + x by ring]
      exact sqEq_add_of_norm_lt (by norm_num) (by rwa [norm_neg, hL])
    exact (hxb'.symm.trans e₂).trans hnL
  · have e₃ : SqEq (x + 3 * L) x := sqEq_add_of_norm_lt (by norm_num) (by linarith [not_lt.mp hlt])
    have hAx : SqEq A x := hxa'.symm.trans e₃
    have hba : SqEq (B * A) x := by rw [mul_comm]; exact hxab.symm
    exact (sqEq_of_mul_sqEq hba hAx hx0).trans ⟨x, hx0, by ring⟩

end Three

section Bad

variable {q : ℕ} [hq : Fact q.Prime]

theorem residue_isSquare_of_padic' {c : ℤ} (hnd : ¬ (q : ℤ) ∣ c) (h : IsSquare (c : ℚ_[q])) :
    IsSquare (c : ZMod q) := by
  have hu : ‖(c : ℤ_[q])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hnd
  obtain ⟨r, -, hr⟩ := exists_padicInt_sq_of_isSquare hu (by rwa [PadicInt.coe_intCast])
  refine ⟨PadicInt.toZMod r, ?_⟩
  have := congrArg PadicInt.toZMod hr
  rwa [map_intCast, map_mul] at this

theorem valuation_eq_zero_of_norm_one {u : ℚ_[q]} (hu : ‖u‖ = 1) : u.valuation = 0 := by
  have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  have hp1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have e := Padic.norm_eq_zpow_neg_valuation hu0
  rw [hu] at e
  have := zpow_right_injective₀ (by linarith) hp1.ne' (e.symm.trans (zpow_zero _).symm)
  simpa using this

theorem lsym_eq_of_isSquare_mul {u w : ℤ} (hu : ¬ (q : ℤ) ∣ u) (hw : ¬ (q : ℤ) ∣ w)
    (h : IsSquare ((u * w : ℤ) : ℚ_[q])) : lsym u q = lsym w q := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  have hnd : ¬ (q : ℤ) ∣ u * w := fun h' => (hqp.dvd_or_dvd h').elim hu hw
  have hsq := residue_isSquare_of_padic' hnd h
  have h0 : lsym (u * w) q = 0 := lsym_of_isSquare hsq
  rw [lsym_mul q (intCast_ne_zero_of_not_dvd hu) (intCast_ne_zero_of_not_dvd hw)] at h0
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact key _ _ h0

theorem padicValInt_q_mul {m : ℤ} (hm : ¬ (q : ℤ) ∣ m) : padicValInt q (q * m) = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  rw [padicValInt.mul (Int.natCast_ne_zero.mpr hq.out.ne_zero) hm0, padicValInt_self,
    padicValInt.eq_zero_of_not_dvd hm, add_zero]

theorem not_isSquare_q_mul {m : ℤ} (hm : ¬ (q : ℤ) ∣ m) : ¬ IsSquare (((q * m : ℤ)) : ℚ_[q]) := by
  intro h
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h0 : (((q * m : ℤ)) : ℚ_[q]) ≠ 0 :=
    Int.cast_ne_zero.mpr (mul_ne_zero (Int.natCast_ne_zero.mpr hq.out.ne_zero) hm0)
  have e := even_valuation_of_isSquare h0 h
  rw [Padic.valuation_intCast, padicValInt_q_mul hm] at e
  exact absurd e (by decide)

/-- Equal square classes in `ℚ_q` give equal `qcls` (squarefree integers, `q` odd). -/
theorem qcls_eq_of_sqEq {u w : ℤ} (hu : Squarefree u) (hw : Squarefree w)
    (h : SqEq (u : ℚ_[q]) (w : ℚ_[q])) : qcls q u = qcls q w := by
  have hsq : IsSquare (((u * w : ℤ)) : ℚ_[q]) := by push_cast; exact h.isSquare_mul
  unfold qcls
  by_cases h1 : (q : ℤ) ∣ u <;> by_cases h2 : (q : ℤ) ∣ w
  · rw [if_pos h1, if_pos h2]
    obtain ⟨u', rfl⟩ := h1
    obtain ⟨w', rfl⟩ := h2
    have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.out.ne_zero
    have hu' : ¬ (q : ℤ) ∣ u' := by
      have := not_dvd_div_of_squarefree hq.out hu (dvd_mul_right _ _)
      rwa [Int.mul_ediv_cancel_left _ hq0] at this
    have hw' : ¬ (q : ℤ) ∣ w' := by
      have := not_dvd_div_of_squarefree hq.out hw (dvd_mul_right _ _)
      rwa [Int.mul_ediv_cancel_left _ hq0] at this
    rw [Int.mul_ediv_cancel_left _ hq0, Int.mul_ediv_cancel_left _ hq0]
    refine Prod.ext rfl (lsym_eq_of_isSquare_mul hu' hw' ?_)
    have hqq : ((q : ℤ) : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr hq0
    rw [← isSquare_mul_sq_iff hqq]
    convert hsq using 1; push_cast; ring
  · exfalso
    obtain ⟨u', rfl⟩ := h1
    have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.out.ne_zero
    have hu' : ¬ (q : ℤ) ∣ u' := by
      have := not_dvd_div_of_squarefree hq.out hu (dvd_mul_right _ _)
      rwa [Int.mul_ediv_cancel_left _ hq0] at this
    have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
    exact not_isSquare_q_mul (m := u' * w) (fun h' => (hqp.dvd_or_dvd h').elim hu' h2)
      (by rw [show (q : ℤ) * (u' * w) = q * u' * w by ring]; exact hsq)
  · exfalso
    obtain ⟨w', rfl⟩ := h2
    have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.out.ne_zero
    have hw' : ¬ (q : ℤ) ∣ w' := by
      have := not_dvd_div_of_squarefree hq.out hw (dvd_mul_right _ _)
      rwa [Int.mul_ediv_cancel_left _ hq0] at this
    have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
    exact not_isSquare_q_mul (m := u * w') (fun h' => (hqp.dvd_or_dvd h').elim h1 hw')
      (by rw [show (q : ℤ) * (u * w') = u * (q * w') by ring]; exact hsq)
  · rw [if_neg h1, if_neg h2]
    exact Prod.ext rfl (lsym_eq_of_isSquare_mul h1 h2 hsq)

theorem sqEq_one_add {t : ℚ_[q]} (hq2 : q ≠ 2) (h : ‖t‖ < 1) : SqEq (1 + t) 1 :=
  sqEq_add_of_norm_lt hq2 (by rwa [norm_one])

/-- **The local image at `q ∣ ℓ` in square classes**: `(a, b)` is one of the torsion classes
`(1, 1)`, `(ℓ, 1)`, `(3, −ℓ)`, `(3ℓ, −ℓ)`. -/
theorem locM_bad_classes (hq2 : q ≠ 2) (hq3 : q ≠ 3) {L A B : ℚ_[q]} (hL : ‖L‖ < 1)
    (hL0 : L ≠ 0) (hvL : L.valuation = 1) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (h : LocM ℚ_[q] L A B) :
    (SqEq A 1 ∧ SqEq B 1) ∨ (SqEq A L ∧ SqEq B 1) ∨ (SqEq A 3 ∧ SqEq B (-L)) ∨
      (SqEq A (3 * L) ∧ SqEq B (-L)) := by
  have hn3 := padic_norm_three (p := q) hq3
  have hn2 := padic_norm_two (p := q) hq2
  have hn4 : ‖(4 : ℚ_[q])‖ = 1 := by
    rw [show (4 : ℚ_[q]) = 2 * 2 by norm_num, norm_mul, hn2, one_mul]
  have hn3L : ‖3 * L‖ = ‖L‖ := by rw [norm_mul, hn3, one_mul]
  have h3 : (3 : ℚ_[q]) ≠ 0 := by norm_num
  have hsqLL : ∀ {X : ℚ_[q]}, SqEq X (L * L) → SqEq X 1 := fun hX =>
    hX.trans ⟨L, hL0, by ring⟩
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact Or.inl ⟨(sqEq_iff_isSquare_mul hA0 one_ne_zero).mpr (by simpa),
      (sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa)⟩
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', hab'⟩ | ⟨-, ha', hab'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · have ha' : SqEq A (-3 * L * -L) := sqEq_of_mul_sqEq hab' hb' (neg_ne_zero.mpr hL0)
    exact Or.inr (Or.inr (Or.inl ⟨ha'.trans ⟨L, hL0, by ring⟩, hb'⟩))
  · have hba : SqEq (B * A) L := by rw [mul_comm]; exact hab'
    exact Or.inr (Or.inl ⟨ha', hsqLL (sqEq_of_mul_sqEq hba ha' hL0)⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨ha', hb'⟩))
  rcases lt_trichotomy ‖x‖ ‖L‖ with hlt | heq | hgt
  · have e₂ : SqEq (x - L) (-L) := by
      rw [show x - L = -L + x by ring]; exact sqEq_add_of_norm_lt hq2 (by rwa [norm_neg])
    have e₃ : SqEq (x + 3 * L) (3 * L) := by
      rw [add_comm]; exact sqEq_add_of_norm_lt hq2 (by rwa [hn3L])
    exact Or.inr (Or.inr (Or.inr ⟨hxa'.symm.trans e₃, hxb'.symm.trans e₂⟩))
  · set t := x / L with ht
    have hxt : x = L * t := by rw [ht]; field_simp
    have hnt : ‖t‖ = 1 := by rw [ht, norm_div, heq, div_self (norm_ne_zero_iff.mpr hL0)]
    have ht0 : t ≠ 0 := by intro h0; rw [h0, norm_zero] at hnt; exact zero_ne_one hnt
    by_cases hm1 : ‖t - 1‖ < 1
    · -- `x ≡ ℓ`
      have et : SqEq t 1 := by
        have := sqEq_one_add hq2 hm1; rwa [show 1 + (t - 1) = t by ring] at this
      have et3 : SqEq (t + 3) 1 := by
        have := sqEq_add_of_norm_lt hq2 (x := (4 : ℚ_[q])) (y := t - 1) (by rwa [hn4])
        rw [show (4 : ℚ_[q]) + (t - 1) = t + 3 by ring] at this
        exact this.trans ⟨2, two_ne_zero, by ring⟩
      have hxL : SqEq x L := by
        rw [hxt]; have := (SqEq.refl L).mul et; rwa [mul_one] at this
      have hx3L : SqEq (x + 3 * L) L := by
        rw [hxt, show L * t + 3 * L = L * (t + 3) by ring]
        have := (SqEq.refl L).mul et3; rwa [mul_one] at this
      have ha' : SqEq A L := hxa'.symm.trans hx3L
      have hba : SqEq (B * A) L := by rw [mul_comm]; exact hxab.symm.trans hxL
      exact Or.inr (Or.inl ⟨ha', hsqLL (sqEq_of_mul_sqEq hba ha' hL0)⟩)
    by_cases hm3 : ‖t + 3‖ < 1
    · -- `x ≡ −3ℓ`
      have et : SqEq t (-3) := by
        have := sqEq_add_of_norm_lt hq2 (x := (-3 : ℚ_[q])) (y := t + 3)
          (by rwa [norm_neg, hn3])
        rwa [show (-3 : ℚ_[q]) + (t + 3) = t by ring] at this
      have et1 : SqEq (t - 1) (-1) := by
        have := sqEq_add_of_norm_lt hq2 (x := (-4 : ℚ_[q])) (y := t + 3)
          (by rwa [norm_neg, hn4])
        rw [show (-4 : ℚ_[q]) + (t + 3) = t - 1 by ring] at this
        exact this.trans ⟨2, two_ne_zero, by ring⟩
      have hx3 : SqEq x (-3 * L) := by
        rw [hxt]; have := (SqEq.refl L).mul et; rwa [show L * -3 = -3 * L by ring] at this
      have hxmL : SqEq (x - L) (-L) := by
        rw [hxt, show L * t - L = L * (t - 1) by ring]
        have := (SqEq.refl L).mul et1; rwa [show L * -1 = -L by ring] at this
      have hb' : SqEq B (-L) := hxb'.symm.trans hxmL
      have ha' : SqEq A (-3 * L * -L) :=
        sqEq_of_mul_sqEq (hxab.symm.trans hx3) hb' (neg_ne_zero.mpr hL0)
      exact Or.inr (Or.inr (Or.inl ⟨ha'.trans ⟨L, hL0, by ring⟩, hb'⟩))
    · -- both units: `x(x − ℓ)(x + 3ℓ) = ℓ³ · unit` is not a square
      exfalso
      have hle : ∀ c : ℚ_[q], ‖c‖ ≤ 1 → ‖t + c‖ ≤ 1 := fun c hc =>
        (Padic.nonarchimedean _ _).trans (max_le hnt.le hc)
      have hu1 : ‖t - 1‖ = 1 := le_antisymm (by
        rw [sub_eq_add_neg]; exact hle _ (by rw [norm_neg, norm_one])) (not_lt.mp hm1)
      have hu3 : ‖t + 3‖ = 1 := le_antisymm (hle _ hn3.le) (not_lt.mp hm3)
      set u := t * (t - 1) * (t + 3)
      have hnu : ‖u‖ = 1 := by simp only [u, norm_mul, hnt, hu1, hu3, mul_one]
      have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hnu; exact zero_ne_one hnu
      -- `x(x − ℓ)(x + 3ℓ) ≡ (ab)² ≡ 1`
      have hprod : SqEq (x * (x - L) * (x + 3 * L)) 1 := by
        have := (hxab.mul hxb').mul hxa'
        refine this.trans ⟨A * B, mul_ne_zero hA0 hB0, by ring⟩
      have hsq : IsSquare (L * u) := by
        have hL2 : L * u * L ^ 2 = x * (x - L) * (x + 3 * L) := by rw [hxt]; simp only [u]; ring
        rw [← isSquare_mul_sq_iff hL0, hL2]
        obtain ⟨s, -, hs⟩ := hprod; exact ⟨s, by rw [hs]; ring⟩
      have e := even_valuation_of_isSquare (mul_ne_zero hL0 hu0) hsq
      rw [Padic.valuation_mul hL0 hu0, hvL, valuation_eq_zero_of_norm_one hnu] at e
      exact absurd e (by decide)
  · have e₂ : SqEq (x - L) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt hq2 (by rwa [norm_neg])
    have e₃ : SqEq (x + 3 * L) x := sqEq_add_of_norm_lt hq2 (by rwa [hn3L])
    have hb' : SqEq B x := hxb'.symm.trans e₂
    have hAx : SqEq A x := hxa'.symm.trans e₃
    have hba : SqEq (B * A) x := by rw [mul_comm]; exact hxab.symm
    have hb1 : SqEq B 1 := (sqEq_of_mul_sqEq hba hAx hx0).trans ⟨x, hx0, by ring⟩
    exact Or.inl ⟨hAx.trans (hb'.symm.trans hb1), hb1⟩

/-- **`LocalBad`, "only if"** (`q ∣ ℓ`, `q ≠ 2, 3`, `ℓ ≡ 11 (mod 12)` squarefree). -/
theorem localBad_nec {ℓ : ℕ} {a b : ℤ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) (hql : q ∣ ℓ)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[q] ℓ a b) : ∃ e₁ e₂ : ZMod 2,
      qcls q a = e₁ • qcls q ℓ + e₂ • qcls q 3 ∧ qcls q b = e₂ • qcls q (-(ℓ : ℤ)) := by
  have hsfZ : Squarefree (ℓ : ℤ) := Int.squarefree_natCast.mpr hsf
  have hsf3 : Squarefree (3 : ℤ) := Int.prime_three.squarefree
  have hsfn : Squarefree (-(ℓ : ℤ)) := by rw [← Int.squarefree_natAbs]; simpa using hsf
  have hsf3l : Squarefree (3 * (ℓ : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_mul, Nat.squarefree_mul_iff]
    refine ⟨?_, Nat.prime_three.squarefree, by simpa using hsf⟩
    rw [show (3 : ℤ).natAbs = 3 from rfl, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    simp only [Int.natAbs_natCast]; omega
  have hsf1 : Squarefree (1 : ℤ) := squarefree_one
  have hqZ : (q : ℤ) ∣ (ℓ : ℤ) := by exact_mod_cast hql
  have hL : ‖((ℓ : ℤ) : ℚ_[q])‖ < 1 := Padic.norm_intCast_lt_one_iff.mpr hqZ
  have hL0 : ((ℓ : ℤ) : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have hvL : (((ℓ : ℤ)) : ℚ_[q]).valuation = 1 := by
    rw [Padic.valuation_intCast]
    obtain ⟨m, hm⟩ := hqZ
    have hm' : ¬ (q : ℤ) ∣ m := by
      have := not_dvd_div_of_squarefree hq.out hsfZ ⟨m, hm⟩
      rwa [hm, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hq.out.ne_zero)] at this
    rw [hm, padicValInt_q_mul hm']; rfl
  have hA0 : (a : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr ha.ne_zero
  have hB0 : (b : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  have h' : LocM ℚ_[q] ((ℓ : ℤ) : ℚ_[q]) a b := by simpa using h
  have c1 : (1 : ℚ_[q]) = ((1 : ℤ) : ℚ_[q]) := by simp
  have c3 : (3 : ℚ_[q]) = ((3 : ℤ) : ℚ_[q]) := by simp
  have c3l : 3 * ((ℓ : ℤ) : ℚ_[q]) = ((3 * (ℓ : ℤ) : ℤ) : ℚ_[q]) := by push_cast; ring
  have cnl : -((ℓ : ℤ) : ℚ_[q]) = ((-(ℓ : ℤ) : ℤ) : ℚ_[q]) := by push_cast; ring
  have q1 : qcls q 1 = 0 := qcls_one q
  have q3l : qcls q (3 * (ℓ : ℤ)) = qcls q 3 + qcls q ℓ := qcls_mul q hsf3l
  rcases locM_bad_classes hq2 hq3 hL hL0 hvL hA0 hB0 h' with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ |
    ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  · rw [c1] at ha' hb'
    refine ⟨0, 0, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsf1 ha', q1]; simp
    · rw [qcls_eq_of_sqEq hb hsf1 hb', q1]; simp
  · rw [c1] at hb'
    refine ⟨1, 0, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsfZ ha']; simp
    · rw [qcls_eq_of_sqEq hb hsf1 hb', q1]; simp
  · rw [c3] at ha'; rw [cnl] at hb'
    refine ⟨0, 1, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsf3 ha']; simp
    · rw [qcls_eq_of_sqEq hb hsfn hb']; simp
  · rw [c3l] at ha'; rw [cnl] at hb'
    refine ⟨1, 1, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsf3l ha', q3l]; simp [add_comm]
    · rw [qcls_eq_of_sqEq hb hsfn hb']; simp

end Bad

end ZInQ.Manuscript.PoleRC
