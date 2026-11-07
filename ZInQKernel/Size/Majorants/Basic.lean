import ZInQKernel.Syntax.Language
import ZInQKernel.Size.Norms.Substitution

/-!
# The height majorant and a finer size scale

Blueprint: `size/majorants/syntax-height.md` (the majorant) and
`size/majorants/majorant-rules.md` (its closure rules).

* `Maj B h P` is the height-`h` majorant of the blueprint: `deg P ≤ 1` and `‖P‖₁ ≤ 1` for
  `h = 0`; `deg P ≤ B^(8h)` and `‖P‖₁ ≤ 2^(B^(8h))` for `h ≥ 1`.
* `Scale B e s P` is a finer scale used to prove majorants: `deg P ≤ 2^s B^e` and
  `‖P‖₁ ≤ 2^(2^s B^e)`. A ring operation raises `s` by one, a substitution adds the exponents
  `e`, and `2^s ≤ B^d` trades `s` for `d` more powers of `B`. Since `B ≥ 2^20` gives
  `B^8 ≥ 2^160`, up to `160` successive operations cost one height level; this is how explicit
  polynomials are bounded without expanding them.

`Maj B h P ↔ Scale B (8h) 0 P` for `h ≥ 1` (`maj_iff_sz`), and `Maj B h P → Scale B (8h) 0 P` for all
`h` (`Maj.sz`).
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {σ τ : Type*}

/-! ### Auxiliary facts -/

theorem totalDegree_list_sum_le' (l : List (MvPolynomial σ ℤ)) (D : ℕ)
    (h : ∀ f ∈ l, f.totalDegree ≤ D) : l.sum.totalDegree ≤ D := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.sum_cons]
    exact (totalDegree_add _ _).trans
      (max_le (h f List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-! ### The majorant -/

/-- **The height-`h` majorant** `Maj_B(h, P)`: `deg P ≤ 1` and `‖P‖₁ ≤ 1` for `h = 0`;
`deg P ≤ B^(8h)` and `‖P‖₁ ≤ 2^(B^(8h))` for `h ≥ 1`. -/
def Maj (B h : ℕ) (P : MvPolynomial σ ℤ) : Prop :=
  if h = 0 then P.totalDegree ≤ 1 ∧ l1 P ≤ 1
  else P.totalDegree ≤ B ^ (8 * h) ∧ l1 P ≤ 2 ^ B ^ (8 * h)

theorem maj_zero_iff {B : ℕ} {P : MvPolynomial σ ℤ} :
    Maj B 0 P ↔ P.totalDegree ≤ 1 ∧ l1 P ≤ 1 := by
  simp [Maj]

theorem maj_iff_of_ne_zero {B h : ℕ} (hh : h ≠ 0) {P : MvPolynomial σ ℤ} :
    Maj B h P ↔ P.totalDegree ≤ B ^ (8 * h) ∧ l1 P ≤ 2 ^ B ^ (8 * h) := by
  simp [Maj, hh]

/-! ### The finer scale -/

/-- `Scale B e s P`: `deg P ≤ 2^s B^e` and `‖P‖₁ ≤ 2^(2^s B^e)`. -/
def Scale (B e s : ℕ) (P : MvPolynomial σ ℤ) : Prop :=
  P.totalDegree ≤ 2 ^ s * B ^ e ∧ l1 P ≤ 2 ^ (2 ^ s * B ^ e)

theorem one_le_scale {B : ℕ} (hB : 1 ≤ B) (e s : ℕ) : 1 ≤ 2 ^ s * B ^ e :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity))

theorem two_pow_le_scale {B : ℕ} (hB : 1 ≤ B) (e s : ℕ) : 2 ^ s ≤ 2 ^ s * B ^ e :=
  Nat.le_mul_of_pos_right _ (by positivity)

theorem scale_mono {B : ℕ} (hB : 1 ≤ B) {e e' s s' : ℕ} (he : e ≤ e') (hs : s ≤ s') :
    2 ^ s * B ^ e ≤ 2 ^ s' * B ^ e' :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hs) (Nat.pow_le_pow_right hB he)

theorem scale_succ (B e s : ℕ) : 2 ^ (s + 1) * B ^ e = 2 * (2 ^ s * B ^ e) := by
  rw [pow_succ]; ring

namespace Scale

variable {B e s : ℕ} {P Q : MvPolynomial σ ℤ}

theorem mono (h : Scale B e s P) (hB : 1 ≤ B) {e' s' : ℕ} (he : e ≤ e') (hs : s ≤ s') :
    Scale B e' s' P :=
  ⟨h.1.trans (scale_mono hB he hs),
    h.2.trans (Nat.pow_le_pow_right (by norm_num) (scale_mono hB he hs))⟩

theorem X (hB : 1 ≤ B) (i : σ) : Scale B e s (X i : MvPolynomial σ ℤ) := by
  refine ⟨?_, ?_⟩
  · rw [totalDegree_X]; exact one_le_scale hB e s
  · rw [l1_X]; exact Nat.one_le_two_pow

theorem C (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ s) :
    Scale B e s (MvPolynomial.C c : MvPolynomial σ ℤ) := by
  refine ⟨?_, ?_⟩
  · rw [totalDegree_C]; exact Nat.zero_le _
  · rw [l1_C]
    exact hc.trans (Nat.pow_le_pow_right (by norm_num) (two_pow_le_scale hB e s))

theorem zero (hB : 1 ≤ B) : Scale B e s (0 : MvPolynomial σ ℤ) := by
  simpa using C (σ := σ) (e := e) (s := s) hB (c := 0) (by simp)

theorem one (hB : 1 ≤ B) : Scale B e s (1 : MvPolynomial σ ℤ) := by
  simpa using C (σ := σ) (e := e) (s := s) hB (c := 1) Nat.one_le_two_pow

theorem intCast (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ s) :
    Scale B e s (c : MvPolynomial σ ℤ) := by
  rw [← eq_intCast (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ) c]
  exact C hB hc

theorem ofNat (hB : 1 ≤ B) (n : ℕ) [n.AtLeastTwo] (hn : n ≤ 2 ^ 2 ^ s) :
    Scale B e s (OfNat.ofNat n : MvPolynomial σ ℤ) := by
  rw [← map_ofNat (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ) n]
  exact C hB (by rw [show (OfNat.ofNat n : ℤ) = ((n : ℕ) : ℤ) from rfl, Int.natAbs_natCast]; exact hn)

theorem neg (h : Scale B e s P) : Scale B e s (-P) := by
  refine ⟨?_, ?_⟩
  · rw [totalDegree_neg]; exact h.1
  · rw [l1_neg]; exact h.2

theorem add (hP : Scale B e s P) (hQ : Scale B e s Q) (hB : 1 ≤ B) : Scale B e (s + 1) (P + Q) := by
  have hM := one_le_scale hB e s
  rw [Scale, scale_succ]
  refine ⟨(totalDegree_add _ _).trans ((max_le hP.1 hQ.1).trans (by omega)), ?_⟩
  refine (l1_add_le _ _).trans ((Nat.add_le_add hP.2 hQ.2).trans ?_)
  rw [← two_mul, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem sub (hP : Scale B e s P) (hQ : Scale B e s Q) (hB : 1 ≤ B) : Scale B e (s + 1) (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg hB

theorem mul (hP : Scale B e s P) (hQ : Scale B e s Q) : Scale B e (s + 1) (P * Q) := by
  rw [Scale, scale_succ]
  refine ⟨(totalDegree_mul _ _).trans (by have := hP.1; have := hQ.1; omega), ?_⟩
  refine (l1_mul_le _ _).trans ((Nat.mul_le_mul hP.2 hQ.2).trans ?_)
  rw [← pow_add, two_mul]

theorem pow (h : Scale B e s P) {n k : ℕ} (hn : n ≤ 2 ^ k) : Scale B e (s + k) (P ^ n) := by
  have hsc : 2 ^ (s + k) * B ^ e = 2 ^ k * (2 ^ s * B ^ e) := by rw [pow_add]; ring
  rw [Scale, hsc]
  refine ⟨(totalDegree_pow _ _).trans ((Nat.mul_le_mul hn h.1)), ?_⟩
  refine (l1_pow_le _ _).trans ((Nat.pow_le_pow_left h.2 n).trans ?_)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hn |>.trans_eq (mul_comm _ _))

/-- A sum of at most `2^(2^s B^e)` terms raises `s` by one. -/
theorem list_sum {l : List (MvPolynomial σ ℤ)} (h : ∀ f ∈ l, Scale B e s f)
    (hlen : l.length ≤ 2 ^ (2 ^ s * B ^ e)) (hB : 1 ≤ B) : Scale B e (s + 1) l.sum := by
  have hM := one_le_scale hB e s
  rw [Scale, scale_succ]
  refine ⟨(totalDegree_list_sum_le' l _ fun f hf => (h f hf).1).trans (by omega), ?_⟩
  refine (l1_list_sum_le l).trans ?_
  have hsum : (l.map l1).sum ≤ l.length * 2 ^ (2 ^ s * B ^ e) := by
    have := List.sum_le_length_nsmul (l.map l1) (2 ^ (2 ^ s * B ^ e))
      (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).2)
    simpa using this
  refine hsum.trans ((Nat.mul_le_mul_right _ hlen).trans ?_)
  rw [← pow_add, two_mul]

/-- A sum of at most `2^s` terms raises `s` by one. -/
theorem list_sum_of_le {l : List (MvPolynomial σ ℤ)} (h : ∀ f ∈ l, Scale B e s f)
    (hlen : l.length ≤ 2 ^ s) (hB : 1 ≤ B) : Scale B e (s + 1) l.sum :=
  list_sum h (hlen.trans ((Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (two_pow_le_scale hB e s)))) hB

/-- A product of at most `2^k` factors raises `s` by `k`. -/
theorem list_prod {l : List (MvPolynomial σ ℤ)} (h : ∀ f ∈ l, Scale B e s f) {k : ℕ}
    (hlen : l.length ≤ 2 ^ k) : Scale B e (s + k) l.prod := by
  have hsc : 2 ^ (s + k) * B ^ e = 2 ^ k * (2 ^ s * B ^ e) := by rw [pow_add]; ring
  rw [Scale, hsc]
  constructor
  · refine (totalDegree_list_prod l).trans ?_
    have := List.sum_le_length_nsmul (l.map totalDegree) (2 ^ s * B ^ e)
      (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).1)
    simp only [List.length_map, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hlen)
  · refine (l1_list_prod_le l).trans ?_
    have := List.prod_le_pow_length (l.map l1) (2 ^ (2 ^ s * B ^ e))
      (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).2)
    rw [List.length_map, ← pow_mul] at this
    exact this.trans (Nat.pow_le_pow_right (by norm_num)
      ((Nat.mul_le_mul_left _ hlen).trans_eq (mul_comm _ _)))

/-- A product of at most `B^d` factors adds `d` to the exponent. -/
theorem list_prod_of_le_pow {l : List (MvPolynomial σ ℤ)} (h : ∀ f ∈ l, Scale B e s f) {d : ℕ}
    (hlen : l.length ≤ B ^ d) : Scale B (e + d) s l.prod := by
  have hsc : 2 ^ s * B ^ (e + d) = B ^ d * (2 ^ s * B ^ e) := by rw [pow_add]; ring
  rw [Scale, hsc]
  constructor
  · refine (totalDegree_list_prod l).trans ?_
    have := List.sum_le_length_nsmul (l.map totalDegree) (2 ^ s * B ^ e)
      (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).1)
    simp only [List.length_map, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hlen)
  · refine (l1_list_prod_le l).trans ?_
    have := List.prod_le_pow_length (l.map l1) (2 ^ (2 ^ s * B ^ e))
      (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).2)
    rw [List.length_map, ← pow_mul] at this
    exact this.trans (Nat.pow_le_pow_right (by norm_num)
      ((Nat.mul_le_mul_left _ hlen).trans_eq (mul_comm _ _)))

/-- **Substitution.** The exponents add and `s` becomes `s + t + 1`. -/
theorem bind₁ {e₁ s₁ e₂ s₂ : ℕ} {P : MvPolynomial σ ℤ} {f : σ → MvPolynomial τ ℤ}
    (hP : Scale B e₁ s₁ P) (hf : ∀ i ∈ P.vars, Scale B e₂ s₂ (f i)) (hB : 1 ≤ B) :
    Scale B (e₁ + e₂) (s₁ + s₂ + 1) (MvPolynomial.bind₁ f P) := by
  set M₁ := 2 ^ s₁ * B ^ e₁
  set M₂ := 2 ^ s₂ * B ^ e₂
  have hM₂ : 1 ≤ M₂ := one_le_scale hB e₂ s₂
  have hsc : 2 ^ (s₁ + s₂ + 1) * B ^ (e₁ + e₂) = 2 * (M₁ * M₂) := by
    simp only [M₁, M₂, pow_add, pow_one]; ring
  have hP1 : P.totalDegree ≤ M₁ := hP.1
  have hP2 : l1 P ≤ 2 ^ M₁ := hP.2
  rw [Scale, hsc]
  constructor
  · refine (Syntax.totalDegree_bind₁_le f P M₂ fun i hi => (hf i hi).1).trans ?_
    exact (Nat.mul_le_mul_right _ hP1).trans (by omega)
  · refine (l1_bind₁_le f P Nat.one_le_two_pow fun i hi => (hf i hi).2).trans ?_
    refine (Nat.mul_le_mul hP2 (Nat.pow_le_pow_right (by norm_num) hP1)).trans ?_
    rw [← pow_mul, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    show M₁ + M₂ * M₁ ≤ 2 * (M₁ * M₂)
    have : M₁ ≤ M₁ * M₂ := Nat.le_mul_of_pos_right _ hM₂
    rw [mul_comm M₂ M₁]
    omega

/-- Renaming keeps the scale. -/
theorem rename (f : σ → τ) (h : Scale B e s P) : Scale B e s (MvPolynomial.rename f P) :=
  ⟨(totalDegree_rename_le f P).trans h.1, (l1_rename_le f P).trans h.2⟩

/-- **Lifting.** `2^s ≤ B^d` trades `s` for `d` more powers of `B`. -/
theorem lift (h : Scale B e s P) {d : ℕ} (hd : 2 ^ s ≤ B ^ d) : Scale B (e + d) 0 P := by
  have hle : 2 ^ s * B ^ e ≤ 2 ^ 0 * B ^ (e + d) := by
    rw [pow_zero, one_mul, pow_add, mul_comm (B ^ e)]
    exact Nat.mul_le_mul_right _ hd
  exact ⟨h.1.trans hle, h.2.trans (Nat.pow_le_pow_right (by norm_num) hle)⟩

end Scale

/-! ### Majorant and scale -/

theorem maj_iff_sz {B h : ℕ} (hh : h ≠ 0) {P : MvPolynomial σ ℤ} :
    Maj B h P ↔ Scale B (8 * h) 0 P := by
  rw [maj_iff_of_ne_zero hh, Scale, pow_zero, one_mul]

theorem Maj.sz {B h : ℕ} {P : MvPolynomial σ ℤ} (hP : Maj B h P) : Scale B (8 * h) 0 P := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [maj_zero_iff] at hP
    refine ⟨by simpa using hP.1, hP.2.trans (by norm_num)⟩
  · exact (maj_iff_sz hh.ne').1 hP

theorem Scale.maj {B h : ℕ} {P : MvPolynomial σ ℤ} (hP : Scale B (8 * h) 0 P) (hh : h ≠ 0) :
    Maj B h P :=
  (maj_iff_sz hh).2 hP

/-- From the finer scale to the majorant: `2^s ≤ B^8` gives one more height level. -/
theorem Scale.maj_succ {B h s : ℕ} {P : MvPolynomial σ ℤ} (hP : Scale B (8 * h) s P)
    (hs : 2 ^ s ≤ B ^ 8) : Maj B (h + 1) P :=
  Scale.maj (by simpa [Nat.mul_succ] using hP.lift hs) (Nat.succ_ne_zero h)

/-- `B ≥ 2^20` gives `2^s ≤ B^8` for `s ≤ 160`. -/
theorem two_pow_le_pow_eight {B s : ℕ} (hB : 2 ^ 20 ≤ B) (hs : s ≤ 160) : 2 ^ s ≤ B ^ 8 :=
  calc 2 ^ s ≤ 2 ^ 160 := Nat.pow_le_pow_right (by norm_num) hs
    _ = (2 ^ 20) ^ 8 := by norm_num
    _ ≤ B ^ 8 := Nat.pow_le_pow_left hB 8

/-- `B ≥ 2^20` gives `2^s ≤ B^4` for `s ≤ 80`. -/
theorem two_pow_le_pow_four {B s : ℕ} (hB : 2 ^ 20 ≤ B) (hs : s ≤ 80) : 2 ^ s ≤ B ^ 4 :=
  calc 2 ^ s ≤ 2 ^ 80 := Nat.pow_le_pow_right (by norm_num) hs
    _ = (2 ^ 20) ^ 4 := by norm_num
    _ ≤ B ^ 4 := Nat.pow_le_pow_left hB 4

end ZInQ.Size
