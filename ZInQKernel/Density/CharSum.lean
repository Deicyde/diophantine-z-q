import Mathlib
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.RouteK.Selmer.CharSum

/-!
# Character sums for the curves `y² = x³ + a x` over `𝔽_p`

File 1 of `docs/research/pd-paper.md` §6 (Lemmas 1.1–1.5 of §1.2). For a prime `p` and
`a ∈ 𝔽_p` put `jac a = φ_p(a) = Σ_x χ(x³ + a x)`, where `χ = quadraticChar (ZMod p)`.

* `pointCount_eq` (Lemma 1.1): `pointCount p a = p + 1 + jac a` for `p ≠ 2`;
* `jac_sq_mul` (Lemma 1.2): `jac (k² a) = χ(k) jac a` for `k ≠ 0`;
* `sum_quadraticChar_shift_mul` (Lemma 1.3): `Σ_t χ((t + α)(t + β)) = -1` for `α ≠ β`, `p ≠ 2`;
* `jacobsthal` (Lemma 1.4): `jac 1 ² + jac r ² = 4p` for `p ≡ 1 (mod 4)` and `r` a non-square,
  and `jac_even`: every `jac a` is even (for `p ≠ 2`);
* `four_dvd_pointCount` (Lemma 1.5): `4 ∣ pointCount p (-D²)` for `D ≠ 0`. The proof is the
  involution `x ↦ -D²/x`; it needs only `p ≠ 2` (for `p ≡ 3 (mod 4)` the involution has no fixed
  points), so `four_dvd_pointCount_of_mod_four` is the form stated in the note.

The second moment `Σ_a jac(a)² = p(p - 1)(1 + χ(-1))` is `ZInQ.RouteK.Selmer.sum_cubicCharSum_sq`,
since `jac a = cubicCharSum (-a)`.
-/

namespace ZInQ.Density

open Finset

/-! ### Two counting lemmas -/

/-- An involution of a finset changes the parity of nothing: `#s ≡ #Fix(τ) (mod 2)`. -/
theorem card_mod_two_eq_card_fixed {α : Type*} [DecidableEq α] (s : Finset α) (τ : α → α)
    (hs : ∀ x ∈ s, τ x ∈ s) (hτ : ∀ x ∈ s, τ (τ x) = x) :
    s.card % 2 = (s.filter fun x => τ x = x).card % 2 := by
  have hsplit := card_filter_add_card_filter_not (s := s) (fun x => τ x = x)
  have heven : ((s.filter fun x => ¬ τ x = x).card : ZMod 2) = 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_involution (fun x _ => τ x) (fun _ _ => by decide) ?_ ?_ ?_
    · intro a ha _
      exact (Finset.mem_filter.mp ha).2
    · intro a ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨hs a h1, ?_⟩
      rw [hτ a h1]
      exact fun h => h2 h.symm
    · intro a ha
      exact hτ a (Finset.mem_filter.mp ha).1
  rw [ZMod.natCast_eq_zero_iff] at heven
  omega

/-- A sum of values in `{-1, 0, 1}` is `2 #{f = 1} - #{f ≠ 0}`. -/
theorem sum_eq_two_mul_card_sub {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ x, f x = 0 ∨ f x = 1 ∨ f x = -1) :
    ∑ x ∈ s, f x = 2 * ((s.filter fun x => f x = 1).card : ℤ) -
      ((s.filter fun x => f x ≠ 0).card : ℤ) := by
  classical
  rw [card_filter, card_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases hf x with h | h | h <;> simp [h]

/-! ### The sum `φ_p` -/

variable {p : ℕ} [Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

theorem ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rwa [ZMod.ringChar_zmod_n]

theorem quadraticChar_zmod_mem (c : ZMod p) : χ c = 0 ∨ χ c = 1 ∨ χ c = -1 :=
  quadraticChar_isQuadratic (ZMod p) c

/-- `φ_p(a) = Σ_x χ(x³ + a x)`. -/
noncomputable def jac (a : ZMod p) : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x)

theorem jac_eq_cubicCharSum (a : ZMod p) : jac a = RouteK.Selmer.cubicCharSum (-a) := by
  unfold jac RouteK.Selmer.cubicCharSum
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ring

/-- **Lemma 1.1.** `pointCount p a = p + 1 + φ_p(a)`. -/
theorem pointCount_eq (hp2 : p ≠ 2) (a : ZMod p) : (pointCount p a : ℤ) = p + 1 + jac a := by
  rw [pointCount_eq_card]
  have hcard : ((univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1).card : ℤ)
      = ∑ x : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 + a * x).card : ℤ) := by
    rw [card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [card_filter]
    push_cast
    rfl
  have hfib : ∀ x : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 + a * x).card : ℤ) =
      χ (x ^ 3 + a * x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts (ringChar_zmod_ne_two hp2)]
    congr 2
    ext y
    simp
  push_cast
  rw [hcard, Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_add_distrib, Finset.sum_const,
    card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  unfold jac
  ring

/-- **Lemma 1.2.** `φ_p(k² a) = χ(k) φ_p(a)` for `k ≠ 0`. -/
theorem jac_sq_mul {k : ZMod p} (hk : k ≠ 0) (a : ZMod p) :
    jac (k ^ 2 * a) = χ k * jac a := by
  rw [jac_eq_cubicCharSum, jac_eq_cubicCharSum, show -(k ^ 2 * a) = -a * k ^ 2 by ring,
    RouteK.Selmer.cubicCharSum_mul_sq _ hk]

/-- `φ_p(0) = 0`. -/
theorem jac_zero (hp2 : p ≠ 2) : jac (0 : ZMod p) = 0 := by
  rw [jac_eq_cubicCharSum, neg_zero, RouteK.Selmer.cubicCharSum_zero (ringChar_zmod_ne_two hp2)]

/-- **Lemma 1.3.** `Σ_t χ((t + α)(t + β)) = -1` for `α ≠ β` (and `p ≠ 2`). -/
theorem sum_quadraticChar_shift_mul (hp2 : p ≠ 2) {α β : ZMod p} (h : α ≠ β) :
    ∑ t : ZMod p, χ ((t + α) * (t + β)) = -1 := by
  have := RouteK.Selmer.sum_quadraticChar_mul_sub (ringChar_zmod_ne_two hp2)
    (e := -α) (e' := -β) (fun h' => h (neg_injective h'))
  simpa only [sub_neg_eq_add] using this

/-- Lemma 1.3 for `α = β`: `Σ_t χ((t + α)²) = p - 1`. -/
theorem sum_quadraticChar_shift_mul_self (α : ZMod p) :
    ∑ t : ZMod p, χ ((t + α) * (t + α)) = p - 1 := by
  have := RouteK.Selmer.sum_quadraticChar_sub_sq (F := ZMod p) (-α)
  simpa only [sub_neg_eq_add, ZMod.card] using this

/-- The second moment: `Σ_a φ_p(a)² = p(p - 1)(1 + χ(-1))`. -/
theorem sum_jac_sq (hp2 : p ≠ 2) :
    ∑ a : ZMod p, jac a ^ 2 = (p : ℤ) * (p - 1) * (1 + χ (-1)) := by
  have h := RouteK.Selmer.sum_cubicCharSum_sq (F := ZMod p) (ringChar_zmod_ne_two hp2)
  rw [ZMod.card] at h
  rw [← h]
  simp only [jac_eq_cubicCharSum]
  exact Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun a => rfl

/-- `φ_p(a)` is even (`p ≠ 2`): the summand is invariant up to `χ(-1)` under `x ↦ -x`, and the
only fixed point `x = 0` has summand `0`. -/
theorem jac_even (hp2 : p ≠ 2) (a : ZMod p) : Even (jac a) := by
  have hF := ringChar_zmod_ne_two hp2
  unfold jac
  rw [sum_eq_two_mul_card_sub _ _ fun x => quadraticChar_zmod_mem _]
  set s := (univ : Finset (ZMod p)).filter fun x => χ (x ^ 3 + a * x) ≠ 0
  have hneg : ∀ x : ZMod p, (-x) ^ 3 + a * (-x) = (-1) * (x ^ 3 + a * x) := fun x => by ring
  have hpar := card_mod_two_eq_card_fixed s (fun x => -x) ?_ (fun x _ => neg_neg x)
  · have hfix : (s.filter fun x => -x = x) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun x hx hx' => ?_
      have hx0 : x = 0 := (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp hx'
      subst hx0
      simp [s] at hx
    rw [hfix, Finset.card_empty] at hpar
    obtain ⟨k, hk⟩ : 2 ∣ s.card := Nat.dvd_of_mod_eq_zero hpar
    refine ⟨((univ.filter fun x => χ (x ^ 3 + a * x) = 1).card : ℤ) - k, ?_⟩
    rw [hk]
    push_cast
    ring
  · intro x hx
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hneg, map_mul]
    exact mul_ne_zero (fun h => neg_ne_zero.mpr (one_ne_zero (α := ZMod p))
      (quadraticChar_eq_zero_iff.mp h)) hx

/-- **Lemma 1.4 (Jacobsthal's identity).** `φ_p(1)² + φ_p(r)² = 4p` for `p ≡ 1 (mod 4)` and `r` a
non-square. -/
theorem jacobsthal (hp4 : p % 4 = 1) {r : ZMod p} (hr : ¬ IsSquare r) :
    jac (1 : ZMod p) ^ 2 + jac r ^ 2 = 4 * p := by
  have hp2 : p ≠ 2 := by omega
  have hF := ringChar_zmod_ne_two hp2
  have hm1 : χ (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      ((ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega))
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr (IsSquare.zero)
  have hχr : χ r = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hr
  have hpt : ∀ a : ZMod p, a ≠ 0 →
      2 * jac a ^ 2 = (1 + χ a) * jac (1 : ZMod p) ^ 2 + (1 - χ a) * jac r ^ 2 := by
    intro a ha
    rcases quadraticChar_dichotomy ha with h | h
    · obtain ⟨k, rfl⟩ := (quadraticChar_one_iff_isSquare ha).mp h
      have hk : k ≠ 0 := by
        rintro rfl
        simp at ha
      have hj := jac_sq_mul hk (1 : ZMod p)
      rw [mul_one, sq] at hj
      rw [h, hj, mul_pow, quadraticChar_sq_one hk]
      ring
    · have hs : IsSquare (a / r) := by
        rw [← quadraticChar_one_iff_isSquare (div_ne_zero ha hr0)]
        have hmul : χ (a / r) * χ r = χ a := by rw [← map_mul, div_mul_cancel₀ a hr0]
        rw [h, hχr] at hmul
        linarith
      obtain ⟨k, hk⟩ := hs
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hk
        exact hk.elim ha hr0
      have ha' : a = k ^ 2 * r := by
        rw [sq, ← hk]
        field_simp
      rw [h, ha', jac_sq_mul hk0, mul_pow, quadraticChar_sq_one hk0]
      ring
  have hsum := sum_jac_sq hp2
  rw [hm1] at hsum
  have h2 : 2 * ∑ a : ZMod p, jac a ^ 2 =
      ∑ a : ZMod p, ((1 + χ a) * jac (1 : ZMod p) ^ 2 + (1 - χ a) * jac r ^ 2) -
        (jac (1 : ZMod p) ^ 2 + jac r ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_erase_add univ _ (mem_univ (0 : ZMod p)),
      ← Finset.sum_erase_add univ (fun a => (1 + χ a) * jac (1 : ZMod p) ^ 2 + (1 - χ a) * jac r ^ 2)
        (mem_univ (0 : ZMod p)),
      Finset.sum_congr rfl fun a ha => hpt a (Finset.ne_of_mem_erase ha)]
    simp only [jac_zero hp2, MulChar.map_zero]
    ring
  have h3 : ∑ a : ZMod p, ((1 + χ a) * jac (1 : ZMod p) ^ 2 + (1 - χ a) * jac r ^ 2) =
      p * (jac (1 : ZMod p) ^ 2 + jac r ^ 2) := by
    simp only [add_mul, sub_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, quadraticChar_sum_zero hF, Finset.sum_const, card_univ, ZMod.card,
      nsmul_eq_mul]
    ring
  rw [hsum, h3] at h2
  have hp1 : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : ((p : ℤ) - 1) * (jac (1 : ZMod p) ^ 2 + jac r ^ 2) = ((p : ℤ) - 1) * (4 * p) := by linarith
  exact mul_left_cancel₀ (by linarith) this

/-- **Lemma 1.5.** `4 ∣ pointCount p (-D²)` for `D ≠ 0` and `p ≠ 2`. Writing `g(x) = x³ - D² x`
and `X = {x : χ(g(x)) = 1}`, `pointCount p (-D²) = 4 + 2 #X`; the involution `τ x = -D²/x`
preserves `X`, and its fixed points in `X` come in pairs `±x`, so `#X` is even. -/
theorem four_dvd_pointCount (hp2 : p ≠ 2) {D : ZMod p} (hD : D ≠ 0) :
    4 ∣ pointCount p (-D ^ 2) := by
  have hF := ringChar_zmod_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  set g : ZMod p → ZMod p := fun x => x ^ 3 + -D ^ 2 * x with hg
  have hgneg : ∀ x, g (-x) = (-1) * g x := fun x => by simp only [hg]; ring
  -- the zeros of `g`
  have hzero : (univ.filter fun x => χ (g x) = 0) = {0, D, -D} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, quadraticChar_eq_zero_iff,
      Finset.mem_insert, Finset.mem_singleton, hg]
    have : x ^ 3 + -D ^ 2 * x = x * ((x - D) * (x + D)) := by ring
    rw [this, mul_eq_zero, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  have hDD : D ≠ -D := fun h => hD ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
  have hcard3 : (univ.filter fun x => χ (g x) = 0).card = 3 := by
    rw [hzero, Finset.card_insert_of_notMem, Finset.card_pair hDD]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hD, fun h => hD (neg_eq_zero.mp h.symm)⟩
  have hcardnz : ((univ.filter fun x => χ (g x) ≠ 0).card : ℤ) = p - 3 := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (ZMod p)))
      (fun x => χ (g x) = 0)
    rw [hcard3, card_univ, ZMod.card] at this
    have h' : ((univ.filter fun x => χ (g x) ≠ 0).card) = p - 3 := by
      simp only [ne_eq] at this ⊢
      omega
    rw [h', Nat.cast_sub (by omega)]
    norm_num
  -- the set `X`
  set X := (univ : Finset (ZMod p)).filter fun x => χ (g x) = 1 with hX
  have hX0 : ∀ x ∈ X, x ≠ 0 := by
    intro x hx h0
    simp [hX, hg, h0] at hx
  set τ : ZMod p → ZMod p := fun x => -D ^ 2 / x with hτ
  have hττ : ∀ x, x ≠ 0 → τ (τ x) = x := by
    intro x hx
    simp only [hτ]
    field_simp
  have hgτ : ∀ x, x ≠ 0 → g (τ x) = (D ^ 2 / x ^ 2) ^ 2 * g x := by
    intro x hx
    simp only [hτ, hg]
    field_simp
    ring
  have hτX : ∀ x ∈ X, τ x ∈ X := by
    intro x hx
    have hx0 := hX0 x hx
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hgτ x hx0, map_mul, quadraticChar_sq_one' (div_ne_zero (pow_ne_zero 2 hD)
      (pow_ne_zero 2 hx0)), one_mul, hx]
  have hparX := card_mod_two_eq_card_fixed X τ hτX fun x hx => hττ x (hX0 x hx)
  -- the fixed points of `τ` in `X` come in pairs `±x`
  set Y := X.filter fun x => τ x = x with hY
  have hYm : ∀ x ∈ Y, x ≠ 0 ∧ χ (g x) = 1 ∧ x ^ 2 = -D ^ 2 := by
    intro x hx
    simp only [hY, hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp [hg] at hx
    refine ⟨hx0, hx.1, ?_⟩
    have h := hx.2
    simp only [hτ] at h
    field_simp at h
    exact h.symm
  have hYneg : ∀ x ∈ Y, -x ∈ Y := by
    intro x hx
    obtain ⟨hx0, hgx, hsq⟩ := hYm x hx
    have hm1 : χ (-1) = 1 := by
      have : (-1 : ZMod p) = (x / D) ^ 2 := by
        rw [div_pow, hsq]
        field_simp
      rw [this, quadraticChar_sq_one' (div_ne_zero hx0 hD)]
    simp only [hY, hX, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [hgneg, map_mul, hm1, hgx, one_mul], ?_⟩
    simp only [hτ]
    rw [div_neg, neg_inj, div_eq_iff hx0, ← sq, hsq]
  have hparY := card_mod_two_eq_card_fixed Y (fun x => -x) hYneg fun x _ => neg_neg x
  have hYfix : (Y.filter fun x => -x = x) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun x hx hx' => ?_
    exact (hYm x hx).1 ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp hx')
  rw [hYfix, Finset.card_empty] at hparY
  rw [hparY] at hparX
  obtain ⟨k, hk⟩ : 2 ∣ X.card := Nat.dvd_of_mod_eq_zero hparX
  -- assemble
  have hj : jac (-D ^ 2) = 2 * (X.card : ℤ) - (p - 3) := by
    unfold jac
    rw [sum_eq_two_mul_card_sub _ _ fun x => quadraticChar_zmod_mem _, ← hcardnz]
  have hpc := pointCount_eq hp2 (-D ^ 2)
  rw [hj, hk] at hpc
  have : ((4 : ℕ) : ℤ) ∣ (pointCount p (-D ^ 2) : ℤ) := ⟨k + 1, by rw [hpc]; push_cast; ring⟩
  exact Int.natCast_dvd_natCast.mp this

/-- Lemma 1.5 in the form of the note (`p ≡ 1 (mod 4)`). -/
theorem four_dvd_pointCount_of_mod_four (hp4 : p % 4 = 1) {D : ZMod p} (hD : D ≠ 0) :
    4 ∣ pointCount p (-D ^ 2) :=
  four_dvd_pointCount (by omega) hD

end ZInQ.Density
