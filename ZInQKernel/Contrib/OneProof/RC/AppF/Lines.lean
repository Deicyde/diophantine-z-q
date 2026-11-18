import Mathlib

/-!
# App F, the local counts behind (O.6): preserved lines and neighbour lattices (tex 9039–9058)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-theta-form`, paragraph "All-index
recurrence and its phases". At a good prime `p` (odd, outside the support) locally
`R_p = M₂(ℤ_p)` and `V_p = 𝔰𝔩₂`. We write a trace-zero matrix by its coordinates `(a, b, c)`,
`y = (a b; c −a)`, so `Q_B(y) = Nrd y = det y = −a² − bc`.

The `p + 1` neighbours of `R_p` are indexed by the lines of `𝔽_p²`, here `Option (ZMod p)`:
`some t` is the line through `(1, t)`, `none` the line through `(0, 1)`. The neighbour belonging to
`L` is `End(Λ_L)`, `Λ_L = {v ∈ ℤ_p² : v̄ ∈ L}`; we use integer vectors (the conditions only involve
residues mod `p²`). `MemNbr p k (a,b,c) L` says `y / p^k ∈ End(Λ_L)`: `y Λ_L ⊆ p^k Λ_L`.

PROVED here:
* `memNbr_zero_iff_some`, `memNbr_zero_iff_none`: an integral `y` lies in the neighbour of `L` iff
  `ȳ` preserves `L`;
* `count0_primitive` (tex 9041–9043): for `ȳ ≠ 0` the number of preserved lines is
  `1 + (−n/p)`, `n = Q_B(y)`, "including the nilpotent case";
* `count0_pdiv` (tex 9043–9044): for `y ∈ pR_p⁰` all `p + 1` lines are preserved;
* `memNbr_one_scale` : `p y / p = y`, so `(p y)/p ∈ End(Λ_L)` iff `y ∈ End(Λ_L)`;
* `count1_primitive` (tex 9045–9054): for primitive `y` with `p² ∣ Q_B(y)`, exactly one neighbour
  (the kernel line of the nilpotent `ȳ`) contains `y / p`;
* `memNbr_two_pdiv` (tex 9045): a primitive `y` never has `y/p²` in a neighbour, so a neighbour's
  vectors lie in `p⁻¹R_p⁰`;
* `memNbr_congr`: `MemNbr p 1` depends only on `y mod p²`.
-/

namespace ZInQ.Manuscript.RC.AppF

open Finset

/-- `v ∈ Λ_L`: the residue of `v` lies on the line `L` (`some t`: through `(1,t)`; `none`: through
`(0,1)`). -/
def InL (p : ℕ) : Option (ZMod p) → ℤ × ℤ → Prop
  | none, v => (p : ℤ) ∣ v.1
  | some t, v => ((v.2 : ℤ) : ZMod p) = t * ((v.1 : ℤ) : ZMod p)

/-- The action of the trace-zero matrix `(a b; c −a)` on a column vector. -/
def act (a b c : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (a * v.1 + b * v.2, c * v.1 - a * v.2)

/-- `y / p^k ∈ End(Λ_L)` for `y = (a b; c −a)`: `y Λ_L ⊆ p^k Λ_L`. -/
def MemNbr (p k : ℕ) (a b c : ℤ) (L : Option (ZMod p)) : Prop :=
  ∀ v, InL p L v → ∃ w : ℤ × ℤ, act a b c v = ((p : ℤ) ^ k * w.1, (p : ℤ) ^ k * w.2) ∧ InL p L w

/-- `y ∈ pR_p`: every coordinate is divisible by `p`. -/
def PDiv (p : ℕ) (a b c : ℤ) : Prop := (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c

open Classical in
/-- The number of neighbours containing `y / p^k`. -/
noncomputable def count (p : ℕ) [NeZero p] (k : ℕ) (a b c : ℤ) : ℤ :=
  ∑ L : Option (ZMod p), if MemNbr p k a b c L then 1 else 0

variable {p : ℕ} [hp : Fact p.Prime]

theorem InL_add_p_mul (L : Option (ZMod p)) (w u : ℤ × ℤ) :
    InL p L (w.1 + p * u.1, w.2 + p * u.2) ↔ InL p L w := by
  cases L with
  | none =>
    simp only [InL]
    constructor
    · intro h; have := dvd_sub h (dvd_mul_right (p : ℤ) u.1); simpa using this
    · intro h; exact dvd_add h (dvd_mul_right _ _)
  | some t => simp [InL]

theorem InL_p_mul (L : Option (ZMod p)) (v : ℤ × ℤ) : InL p L ((p : ℤ) * v.1, (p : ℤ) * v.2) := by
  cases L with
  | none => exact dvd_mul_right _ _
  | some t => simp [InL]

/-- `MemNbr p k` at `k = 0` reduces to `InL` of the image. -/
theorem memNbr_zero_iff (a b c : ℤ) (L : Option (ZMod p)) :
    MemNbr p 0 a b c L ↔ ∀ v, InL p L v → InL p L (act a b c v) := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, hwL⟩ := h v hv
    simp only [pow_zero, one_mul] at hw
    rw [hw]; exact hwL
  · intro h v hv
    exact ⟨act a b c v, by simp, h v hv⟩

/-- **PROVED (tex 9039–9041).** The line through `(1,t)` is preserved by `ȳ` iff
`b t² + 2 a t − c = 0` in `𝔽_p`. -/
theorem memNbr_zero_iff_some (a b c : ℤ) (t : ZMod p) :
    MemNbr p 0 a b c (some t) ↔ (b : ZMod p) * t ^ 2 + 2 * (a : ZMod p) * t - (c : ZMod p) = 0 := by
  rw [memNbr_zero_iff]
  constructor
  · intro h
    have := h (1, (t.val : ℤ)) (by simp [InL])
    simp only [InL, act] at this
    push_cast at this
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at this
    linear_combination -this
  · intro h v hv
    simp only [InL, act] at hv ⊢
    push_cast at hv ⊢
    rw [hv]
    linear_combination (-(v.1 : ZMod p)) * h

/-- **PROVED (tex 9039–9041).** The line through `(0,1)` is preserved by `ȳ` iff `p ∣ b`. -/
theorem memNbr_zero_iff_none (a b c : ℤ) : MemNbr p 0 a b c none ↔ (p : ℤ) ∣ b := by
  rw [memNbr_zero_iff]
  constructor
  · intro h
    have := h (0, 1) (by simp [InL])
    simpa [InL, act] using this
  · intro h v hv
    simp only [InL, act] at hv ⊢
    exact dvd_add (dvd_mul_of_dvd_right hv _) (dvd_mul_of_dvd_left h _)

theorem intCast_eq_zero_iff_dvd' (x : ℤ) : ((x : ℤ) : ZMod p) = 0 ↔ (p : ℤ) ∣ x :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x p

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

open Classical in
/-- The number of roots of `b t² + 2 a t − c` in `𝔽_p`, `b ≠ 0`, is `1 + χ(a² + bc)`. -/
theorem card_roots_quadratic (hp2 : p ≠ 2) {a b c : ZMod p} (hb : b ≠ 0) :
    (#(univ.filter (fun t : ZMod p => b * t ^ 2 + 2 * a * t - c = 0)) : ℤ) =
      1 + quadraticChar (ZMod p) (a ^ 2 + b * c) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have key := quadraticChar_card_sqrts hchar (a ^ 2 + b * c)
  rw [add_comm (1 : ℤ), ← key]
  congr 1
  rw [Set.toFinset_ofPred]
  apply Finset.card_bij (fun t _ => b * t + a)
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    linear_combination b * ht
  · intro t₁ _ t₂ _ h
    have : b * (t₁ - t₂) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hb
    · exact sub_eq_zero.mp h'
  · intro u hu
    refine ⟨(u - a) / b, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hu ⊢
      field_simp
      linear_combination hu
    · field_simp; ring

open Classical in
theorem count_eq (k : ℕ) (a b c : ℤ) :
    count p k a b c = (if MemNbr p k a b c none then 1 else 0) +
      (#(univ.filter (fun t : ZMod p => MemNbr p k a b c (some t))) : ℤ) := by
  unfold count
  rw [Fintype.sum_option]
  congr 1
  rw [Finset.card_filter]; push_cast; rfl

/-- **PROVED (tex 9041–9043): `1 + (−n/p)` preserved lines.** For an odd prime `p` and a trace-zero
`y = (a b; c −a)` with nonzero reduction, the number of lines of `𝔽_p²` preserved by `ȳ` (the
neighbours containing `y`) is `1 + (−n/p)`, `n = Q_B(y) = −a² − bc`, including the nilpotent case. -/
theorem count0_primitive (hp2 : p ≠ 2) {a b c : ℤ} (hprim : ¬ PDiv p a b c) :
    count p 0 a b c = 1 + legendreSym p (-(-a ^ 2 - b * c)) := by
  classical
  rw [count_eq]
  have hneg : (-(-a ^ 2 - b * c) : ℤ) = a ^ 2 + b * c := by ring
  rw [hneg, legendreSym]
  simp only [memNbr_zero_iff_some, memNbr_zero_iff_none]
  push_cast
  by_cases hb : (p : ℤ) ∣ b
  · have hb0 : ((b : ℤ) : ZMod p) = 0 := (intCast_eq_zero_iff_dvd' b).mpr hb
    rw [if_pos hb, hb0]
    simp only [zero_mul, zero_add]
    by_cases ha : (p : ℤ) ∣ a
    · have ha0 : ((a : ℤ) : ZMod p) = 0 := (intCast_eq_zero_iff_dvd' a).mpr ha
      have hc : ¬ (p : ℤ) ∣ c := fun hc => hprim ⟨ha, hb, hc⟩
      have hc0 : ((c : ℤ) : ZMod p) ≠ 0 := fun h => hc ((intCast_eq_zero_iff_dvd' c).mp h)
      rw [ha0]
      simp [hc0]
    · have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := fun h => ha ((intCast_eq_zero_iff_dvd' a).mp h)
      have h2 := two_ne_zero_zmod hp2
      have hsq : quadraticChar (ZMod p) ((a : ZMod p) ^ 2) = 1 :=
        quadraticChar_sq_one' ha0
      rw [add_zero, hsq]
      have : univ.filter (fun t : ZMod p => 2 * (a : ZMod p) * t - (c : ZMod p) = 0) =
          {(c : ZMod p) / (2 * a)} := by
        ext t
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro h; field_simp; linear_combination h
        · intro h; rw [h]; field_simp; ring
      rw [this]; simp
  · have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := fun h => hb ((intCast_eq_zero_iff_dvd' b).mp h)
    rw [if_neg hb, card_roots_quadratic hp2 hb0]
    ring

/-- **PROVED (tex 9043–9044).** For `y ∈ pR_p⁰` all `p + 1` lines are preserved (the excess over
`1 + (−n/p) = 1` is `p`). -/
theorem count0_pdiv {a b c : ℤ} (h : PDiv p a b c) : count p 0 a b c = p + 1 := by
  classical
  have hall : ∀ L, MemNbr p 0 a b c L := by
    intro L
    rw [memNbr_zero_iff]
    intro v _
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := h
    have : act (p * a') (p * b') (p * c') v = ((p : ℤ) * (a' * v.1 + b' * v.2),
        (p : ℤ) * (c' * v.1 - a' * v.2)) := by simp only [act]; ext <;> ring
    rw [this]; exact InL_p_mul L (a' * v.1 + b' * v.2, c' * v.1 - a' * v.2)
  unfold count
  simp only [hall, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_option,
    ZMod.card, nsmul_eq_mul, mul_one]
  push_cast; ring

/-- **PROVED.** `(p y)/p = y`: `MemNbr p 1 (p a, p b, p c) L ↔ MemNbr p 0 a b c L`. -/
theorem memNbr_one_scale (a b c : ℤ) (L : Option (ZMod p)) :
    MemNbr p 1 (p * a) (p * b) (p * c) L ↔ MemNbr p 0 a b c L := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hact : ∀ v, act (p * a) (p * b) (p * c) v = ((p : ℤ) * (act a b c v).1,
      (p : ℤ) * (act a b c v).2) := by intro v; simp only [act]; ext <;> ring
  constructor
  · intro h
    rw [memNbr_zero_iff]
    intro v hv
    obtain ⟨w, hw, hwL⟩ := h v hv
    rw [hact, pow_one] at hw
    have e1 : (act a b c v).1 = w.1 := mul_left_cancel₀ hp0 (congrArg Prod.fst hw)
    have e2 : (act a b c v).2 = w.2 := mul_left_cancel₀ hp0 (congrArg Prod.snd hw)
    have : act a b c v = w := Prod.ext e1 e2
    rw [this]; exact hwL
  · intro h v hv
    rw [memNbr_zero_iff] at h
    exact ⟨act a b c v, by rw [hact, pow_one], h v hv⟩

/-- **PROVED.** `MemNbr p 1` depends only on `y mod p²` (as `Λ_L ⊇ pℤ_p²`). -/
theorem memNbr_congr {a b c a' b' c' : ℤ} (ha : (p : ℤ) ^ 2 ∣ a - a') (hb : (p : ℤ) ^ 2 ∣ b - b')
    (hc : (p : ℤ) ^ 2 ∣ c - c') (L : Option (ZMod p)) :
    MemNbr p 1 a b c L ↔ MemNbr p 1 a' b' c' L := by
  have key : ∀ {a b c a' b' c' : ℤ}, (p : ℤ) ^ 2 ∣ a - a' → (p : ℤ) ^ 2 ∣ b - b' →
      (p : ℤ) ^ 2 ∣ c - c' → MemNbr p 1 a b c L → MemNbr p 1 a' b' c' L := by
    intro a b c a' b' c' ha hb hc h v hv
    obtain ⟨w, hw, hwL⟩ := h v hv
    obtain ⟨α, hα⟩ := ha; obtain ⟨β, hβ⟩ := hb; obtain ⟨γ, hγ⟩ := hc
    refine ⟨(w.1 - p * (α * v.1 + β * v.2), w.2 - p * (γ * v.1 - α * v.2)), ?_, ?_⟩
    · have h1 := congrArg Prod.fst hw; have h2 := congrArg Prod.snd hw
      simp only [act, pow_one] at h1 h2 ⊢
      ext
      · simp only; linear_combination h1 - v.1 * hα - v.2 * hβ
      · simp only; linear_combination h2 - v.1 * hγ + v.2 * hα
    · have := (InL_add_p_mul L w (-(α * v.1 + β * v.2), -(γ * v.1 - α * v.2))).mpr hwL
      convert this using 2 <;> ring
  constructor
  · exact key ha hb hc
  · exact key (by rw [← dvd_neg, neg_sub]; exact ha) (by rw [← dvd_neg, neg_sub]; exact hb)
      (by rw [← dvd_neg, neg_sub]; exact hc)

/-- A neighbour containing `y/p` contains the image of `y` (as `pℤ_p² ⊆ Λ_L`). -/
theorem InL_act_of_memNbr_one {a b c : ℤ} {L : Option (ZMod p)} (h : MemNbr p 1 a b c L)
    (v : ℤ × ℤ) : InL p L (act a b c v) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨w, hw, hwL⟩ := h ((p : ℤ) * v.1, (p : ℤ) * v.2) (InL_p_mul L v)
  have h1 := congrArg Prod.fst hw; have h2 := congrArg Prod.snd hw
  simp only [act, pow_one] at h1 h2
  have e : act a b c v = w := by
    ext
    · exact mul_left_cancel₀ hp0 (by simp only [act]; linear_combination h1)
    · exact mul_left_cancel₀ hp0 (by simp only [act]; linear_combination h2)
  rw [e]; exact hwL

/-- **PROVED (tex 9045–9054): the nonintegral neighbour.** For primitive trace-zero `y` with
`p² ∣ Q_B(y)` (`Q_B(y) = p²n`), exactly one neighbour contains `y / p`: the kernel line of the
nonzero nilpotent `ȳ`. -/
theorem count1_primitive {a b c : ℤ} (hprim : ¬ PDiv p a b c)
    (hdet : (p : ℤ) ^ 2 ∣ -a ^ 2 - b * c) : count p 1 a b c = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hdet1 : (p : ℤ) ∣ a ^ 2 + b * c := by
    have := dvd_trans (dvd_pow_self (p : ℤ) two_ne_zero) hdet
    have := dvd_neg.mpr this; convert this using 1; ring
  -- the unique line `L₀`
  by_cases hb : (p : ℤ) ∣ b
  · -- `p ∣ b`: then `p ∣ a`, `p ∤ c`, `p² ∣ b`; `L₀ = none`
    have ha : (p : ℤ) ∣ a := by
      have : (p : ℤ) ∣ a ^ 2 := by
        have := dvd_sub hdet1 (dvd_mul_of_dvd_left hb c); simpa using this
      exact hpZ.dvd_of_dvd_pow this
    have hc : ¬ (p : ℤ) ∣ c := fun hc => hprim ⟨ha, hb, hc⟩
    have hb2 : (p : ℤ) ^ 2 ∣ b := by
      have ha2 : (p : ℤ) ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd ha 2
      have hbc : (p : ℤ) ^ 2 ∣ b * c := by
        have := dvd_add hdet ha2
        have := dvd_neg.mpr this; convert this using 1; ring
      have hcop : IsCoprime ((p : ℤ) ^ 2) c :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).mpr hc)
      exact hcop.dvd_of_dvd_mul_right hbc
    have hiff : ∀ L, MemNbr p 1 a b c L ↔ L = none := by
      intro L
      constructor
      · intro h
        cases L with
        | none => rfl
        | some t =>
          exfalso
          have := InL_act_of_memNbr_one h (1, 0)
          simp only [InL, act] at this
          push_cast at this
          have ha0 : ((a : ℤ) : ZMod p) = 0 := (intCast_eq_zero_iff_dvd' a).mpr ha
          rw [ha0] at this
          simp only [mul_one, mul_zero, sub_zero, add_zero] at this
          exact hc ((intCast_eq_zero_iff_dvd' c).mp this)
      · rintro rfl v hv
        simp only [InL] at hv
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', hb'⟩ := hb2
        obtain ⟨v1, hv1⟩ := hv
        refine ⟨(a' * v.1 + p * b' * v.2, c * v1 - a' * v.2), ?_, ?_⟩
        · simp only [act, pow_one]
          ext
          · simp only; rw [hb']; ring
          · simp only; rw [hv1]; ring
        · simp only [InL]
          rw [hv1]
          exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
            (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
    unfold count
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · -- `p ∤ b`: `L₀ = some (−a/b)`
    have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := fun h => hb ((intCast_eq_zero_iff_dvd' b).mp h)
    set t₀ : ZMod p := -((a : ℤ) : ZMod p) / ((b : ℤ) : ZMod p) with ht₀
    have hiff : ∀ L, MemNbr p 1 a b c L ↔ L = some t₀ := by
      intro L
      constructor
      · intro h
        have := InL_act_of_memNbr_one h (0, 1)
        cases L with
        | none => exact absurd (by simpa [InL, act] using this) hb
        | some t =>
          simp only [InL, act] at this
          push_cast at this
          simp only [mul_zero, zero_add, mul_one, zero_sub] at this
          congr 1
          rw [ht₀]; field_simp; linear_combination -this
      · rintro rfl v hv
        simp only [InL] at hv
        -- both coordinates of `y v` are divisible by `p`
        have hd1 : (p : ℤ) ∣ a * v.1 + b * v.2 := by
          rw [← intCast_eq_zero_iff_dvd']; push_cast; rw [hv, ht₀]; field_simp; ring
        have hdet0 : ((a : ℤ) : ZMod p) ^ 2 + (b : ZMod p) * (c : ZMod p) = 0 := by
          have := (intCast_eq_zero_iff_dvd' _).mpr hdet1; push_cast at this; exact this
        have hd2 : (p : ℤ) ∣ c * v.1 - a * v.2 := by
          rw [← intCast_eq_zero_iff_dvd']; push_cast; rw [hv, ht₀]; field_simp
          linear_combination (v.1 : ZMod p) * hdet0
        obtain ⟨w1, hw1⟩ := hd1
        obtain ⟨w2, hw2⟩ := hd2
        refine ⟨(w1, w2), by simp only [act, pow_one]; ext <;> simp [hw1, hw2], ?_⟩
        simp only [InL]
        -- `p (b w₂ + a w₁) = (a² + bc) v₁`, divisible by `p²`
        obtain ⟨k, hk⟩ := hdet
        have hlin : (p : ℤ) * (b * w2 + a * w1) = (p : ℤ) * ((p : ℤ) * (-k * v.1)) := by
          rw [mul_add, ← mul_assoc, mul_comm (p : ℤ) b, mul_assoc, ← hw2, ← mul_assoc,
            mul_comm (p : ℤ) a, mul_assoc, ← hw1]
          linear_combination (-v.1) * hk
        have hlin' := mul_left_cancel₀ hp0 hlin
        have hz : ((b : ℤ) : ZMod p) * (w2 : ZMod p) + (a : ZMod p) * (w1 : ZMod p) = 0 := by
          have := congrArg (fun x : ℤ => (x : ZMod p)) hlin'
          push_cast at this; rw [this]; simp
        rw [ht₀]; field_simp; linear_combination hz
    unfold count
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **PROVED (tex 9045, "a nonintegral `x` in a neighbour lies in `p⁻¹R_p⁰`").** If `y/p²` lies in
a neighbour then `y ∈ pR_p`; so a primitive `y` never gives a vector `y/p²` of a neighbour. -/
theorem memNbr_two_pdiv {a b c : ℤ} {L : Option (ZMod p)} (h : MemNbr p 2 a b c L) :
    PDiv p a b c := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- `y (p v) ∈ p² Λ_L ⊆ p² ℤ²` for every `v`, so `y v ∈ p ℤ²`
  have hcol : ∀ v : ℤ × ℤ, (p : ℤ) ∣ (act a b c v).1 ∧ (p : ℤ) ∣ (act a b c v).2 := by
    intro v
    obtain ⟨w, hw, -⟩ := h ((p : ℤ) * v.1, (p : ℤ) * v.2) (InL_p_mul L v)
    have h1 := congrArg Prod.fst hw; have h2 := congrArg Prod.snd hw
    simp only [act] at h1 h2
    refine ⟨⟨w.1, mul_left_cancel₀ hp0 ?_⟩, ⟨w.2, mul_left_cancel₀ hp0 ?_⟩⟩
    · simp only [act]; linear_combination h1
    · simp only [act]; linear_combination h2
  have e1 := hcol (1, 0); have e2 := hcol (0, 1)
  simp only [act, mul_one, mul_zero, add_zero, sub_zero, zero_add, zero_sub] at e1 e2
  exact ⟨e1.1, e2.1, e1.2⟩

end ZInQ.Manuscript.RC.AppF
