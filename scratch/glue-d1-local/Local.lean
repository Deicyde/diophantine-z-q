import Mathlib

/-!
# glue-conductor: the elementary core of Glazer's uniform conductor bound (D1, D3, D4)

Manuscript `diophantine_zq.tex` L796-851 (h-trust steps D1-D4). Everything here is about
integers and rationals; the ramification data enter as the sequence `g i = |G_i|` of orders
of the lower ramification groups of a finite Galois extension of local fields at one prime
(`g 0 = e`, `g` antitone, `g i ≥ 1`, `g i = 1` for large `i`), as in Serre, *Corps locaux*,
IV §§1-3. The dictionary to the field-theoretic objects is:

* Hilbert's formula: `δ = v_P(𝔇) = ∑_{i ≥ 0} (|G_i| - 1)` (Serre IV §1 Prop. 4);
* Herbrand's function at an integer lower index `m ≥ 0`: `φ(m) = ∑_{i=1}^m |G_i|/|G_0|`
  (Serre IV §3), so the upper index of the lower break `b` is `φ b`;
* `G^u = G_i` for `φ(i-1) < u ≤ φ(i)`, so `∫ (1 - |G^u|⁻¹) du` is the sum of
  `(φ i - φ (i-1)) (1 - 1/|G_i|)`.

No `sorry`.
-/

namespace GlueConductor

open Finset

/-- Herbrand's `φ` at an integer lower index `m`: `φ(m) = ∑_{i=1}^m g_i / g_0`. -/
def phi (g : ℕ → ℕ) (m : ℕ) : ℚ := ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0

/-- The different exponent through Hilbert's formula, truncated at `n`:
`δ = ∑_{i<n} (g_i - 1)` (equal to the full sum once `g i = 1` for `i ≥ n`). -/
def delta (g : ℕ → ℕ) (n : ℕ) : ℚ := ∑ i ∈ range n, ((g i : ℚ) - 1)

lemma phi_zero (g : ℕ → ℕ) : phi g 0 = 0 := by simp [phi]

lemma phi_succ (g : ℕ → ℕ) (m : ℕ) : phi g (m + 1) = phi g m + (g (m + 1) : ℚ) / g 0 := by
  unfold phi
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma phi_mono (g : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') : phi g m ≤ phi g m' := by
  unfold phi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i _ _; positivity

/-- **The Herbrand integral (step-function form).** For `n ≥ 0`,
`δ_{n+1}/e = 1 - 1/e + ∑_{i=1}^n (φ(i) - φ(i-1)) (1 - 1/|G_i|)`, i.e.
`δ/e = 1 - 1/e + ∫₀^∞ (1 - |G^u|⁻¹) du` (N5 L807-808). -/
theorem herbrand_integral (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    delta g (n + 1) / g 0 =
      1 - 1 / (g 0 : ℚ) + ∑ i ∈ Icc 1 n, (phi g i - phi g (i - 1)) * (1 - 1 / (g i : ℚ)) := by
  have hpos : ∀ i, (0 : ℚ) < g i := fun i => by exact_mod_cast hg i
  induction n with
  | zero =>
    simp only [delta]
    simp
    have := hpos 0
    field_simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    simp only [delta, Finset.sum_range_succ _ (n + 1)]
    rw [show n + 1 - 1 = n by omega, phi_succ]
    have := hpos 0
    have := hpos (n + 1)
    field_simp
    ring

/-- `φ(m) ≤ m` (the slopes of `φ` are at most one), hence `ψ(u) ≥ u`; this is the elementary
half of the subgroup formula `ψ_{F/ℚ₂}(u) ≥ u` (N5 L838-840). -/
theorem phi_le_self (g : ℕ → ℕ) (hg0 : 0 < g 0) (hanti : Antitone g) (m : ℕ) :
    phi g m ≤ m := by
  induction m with
  | zero => simp [phi_zero]
  | succ m ih =>
    rw [phi_succ]
    have h1 : (g (m + 1) : ℚ) ≤ g 0 := by exact_mod_cast hanti (Nat.zero_le _)
    have h2 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
    have : (g (m + 1) : ℚ) / g 0 ≤ 1 := (div_le_one h2).mpr h1
    push_cast; linarith

/-- **D1, break bound.** If `G_i ≠ 1` (i.e. `g i ≥ 2`) for all `i ≤ b`, then the upper index
`φ(b)` of the lower index `b` is at most `2δ/e`: before the last break the integrand
`1 - |G^u|⁻¹` is at least `1/2` (N5 L809-812). Here `δ = δ_n` for any `n > b`. -/
theorem phi_le_two_delta (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : ∀ i ≤ b, 2 ≤ g i)
    (hbn : b < n) : phi g b ≤ 2 * delta g n / g 0 := by
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have key : (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ 2 * delta g n := by
    calc (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ ∑ i ∈ range (b + 1), (g i : ℚ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
          · intro i _ _; positivity
      _ ≤ ∑ i ∈ range (b + 1), 2 * ((g i : ℚ) - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have : (2 : ℚ) ≤ g i := by
            exact_mod_cast hb i (by simp only [Finset.mem_range] at hi; omega)
          linarith
      _ = 2 * ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * delta g n := by
          unfold delta
          have : ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) ≤ ∑ i ∈ range n, ((g i : ℚ) - 1) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_subset_range.mpr hbn
            · intro i _ _
              have : (1 : ℚ) ≤ g i := by exact_mod_cast hg i
              linarith
          linarith
  unfold phi
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right key h0.le

/-! ## D1's arithmetic: `δ ≤ e - 1 + e v_p(e)` and `e ≤ a!` give `2δ/e ≤ 4a²` -/

/-- `a! ≤ 2^(a²)`. -/
lemma factorial_le_two_pow_sq (a : ℕ) : a.factorial ≤ 2 ^ (a ^ 2) := by
  calc a.factorial ≤ a ^ a := Nat.factorial_le_pow a
    _ ≤ (2 ^ a) ^ a := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le a
    _ = 2 ^ (a ^ 2) := by rw [← pow_mul, sq]

/-- `v_p(e) ≤ log₂ e`. -/
lemma padicValNat_le_log_two {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    padicValNat p e ≤ Nat.log 2 e := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ padicValNat p e ≤ p ^ padicValNat p e := Nat.pow_le_pow_left hp.two_le _
    _ ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) pow_padicValNat_dvd

/-- `1 + log₂(a!) ≤ 2a²` for `a ≥ 1`, the manuscript's `2(1 + log₂ a!) ≤ 4a²`. -/
lemma one_add_log_factorial_le (a : ℕ) (ha : 1 ≤ a) : 1 + Nat.log 2 a.factorial ≤ 2 * a ^ 2 := by
  have h1 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  omega

/-- `v_p(e) ≤ a²` when `e ≤ a!`. -/
lemma padicValNat_le_sq {p e a : ℕ} (hp : p.Prime) (he : e ≠ 0) (hea : e ≤ a.factorial) :
    padicValNat p e ≤ a ^ 2 := by
  have := padicValNat_le_log_two hp he
  have h1 : Nat.log 2 e ≤ Nat.log 2 a.factorial := Nat.log_mono_right hea
  have h2 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  omega

/-- **D1, arithmetic.** If `δ ≤ e - 1 + e·v_p(e)` (Serre's different bound) and `e ≤ a!`
(the normal closure of a degree-`a` extension has degree at most `a!`), then
`2δ ≤ 2(1 + log₂ a!)·e ≤ 4a²·e`. -/
theorem two_delta_le (p e a δ : ℕ) (hp : p.Prime) (he : 1 ≤ e) (ha : 1 ≤ a)
    (hea : e ≤ a.factorial) (hδ : δ ≤ e - 1 + e * padicValNat p e) :
    2 * δ ≤ 2 * (1 + Nat.log 2 a.factorial) * e ∧ 2 * (1 + Nat.log 2 a.factorial) * e ≤ 4 * a ^ 2 * e := by
  have hv : padicValNat p e ≤ Nat.log 2 a.factorial :=
    (padicValNat_le_log_two hp (by omega)).trans (Nat.log_mono_right hea)
  have hl := one_add_log_factorial_le a ha
  constructor
  · have : e * padicValNat p e ≤ e * Nat.log 2 a.factorial := Nat.mul_le_mul_left e hv
    have h2 : e - 1 + e * padicValNat p e ≤ e * (1 + Nat.log 2 a.factorial) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc 2 * δ ≤ 2 * (e * (1 + Nat.log 2 a.factorial)) := by omega
      _ = 2 * (1 + Nat.log 2 a.factorial) * e := by ring
  · have : 2 * (1 + Nat.log 2 a.factorial) ≤ 4 * a ^ 2 := by omega
    exact Nat.mul_le_mul_right e this

/-- **D1, combined.** Let `g i = |G_i|` be the lower ramification data of a finite Galois
extension of `ℚ_p`-local fields with `e = g 0 ≤ a!`, let `b` be a lower index with `G_b ≠ 1`
(e.g. the last break), and suppose the different exponent `δ = ∑_{i<n}(g_i - 1)` (Hilbert)
satisfies Serre's bound `δ ≤ e - 1 + e v_p(e)`. Then the upper index of `b` is at most
`4a²`: `u_last ≤ 2δ/e ≤ 4a²` (N5 L796-812). -/
theorem upper_break_le (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (g : ℕ → ℕ) (hanti : Antitone g)
    (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : 2 ≤ g b) (hbn : b < n) (hea : g 0 ≤ a.factorial)
    (hSerre : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0)) :
    phi g b ≤ 4 * a ^ 2 := by
  have hb' : ∀ i ≤ b, 2 ≤ g i := fun i hi => hb.trans (hanti hi)
  have h1 := phi_le_two_delta g hg b n hb' hbn
  have hδ : delta g n = ((∑ i ∈ range n, (g i - 1) : ℕ) : ℚ) := by
    unfold delta
    push_cast [Nat.cast_sub (hg _)]
    rfl
  obtain ⟨h2, h3⟩ := two_delta_le p (g 0) a _ hp (hg 0) ha hea hSerre
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have h4 : (2 * delta g n : ℚ) ≤ 4 * a ^ 2 * g 0 := by
    rw [hδ]; exact_mod_cast h2.trans h3
  calc phi g b ≤ 2 * delta g n / g 0 := h1
    _ ≤ 4 * a ^ 2 * g 0 / g 0 := div_le_div_of_nonneg_right h4 h0.le
    _ = 4 * a ^ 2 := by field_simp

/-! ## D4: conductor exponents -/

/-- **D4, Swan term.** For a representation of dimension two through a finite Galois
extension with lower ramification data `g`, the Swan conductor is
`∑_{i ≥ 1} (|G_i|/|G_0|) codim V^{G_i}` (Serre VI §2). If every `G_i` with upper index
`φ(i) > U` acts trivially (`c i = 0`), and `c i ≤ 2`, then `Sw ≤ 2U` (N5 L845-846). -/
theorem swan_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc2 : ∀ i, c i ≤ 2) (htriv : ∀ i, U < phi g i → c i = 0) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 * U := by
  classical
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
  set s := (Icc 1 n).filter (fun i => phi g i ≤ U) with hs
  have step1 : ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ ∑ i ∈ s, 2 * ((g i : ℚ) / g 0) := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    have hq : (0 : ℚ) ≤ (g i : ℚ) / g 0 := by positivity
    split_ifs with h
    · nlinarith [hc2 i]
    · rw [htriv i (lt_of_not_ge h), mul_zero]
  have step2 : ∑ i ∈ s, (g i : ℚ) / g 0 ≤ U := by
    rcases s.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact hU
    · obtain ⟨m, hm, hmax⟩ := s.exists_max_image id hne
      have hsub : s ⊆ Icc 1 m := by
        intro i hi
        have h1 := (Finset.mem_filter.mp hi).1
        simp only [Finset.mem_Icc] at h1 ⊢
        exact ⟨h1.1, hmax i hi⟩
      calc ∑ i ∈ s, (g i : ℚ) / g 0 ≤ ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ = phi g m := rfl
        _ ≤ U := (Finset.mem_filter.mp hm).2
  rw [← Finset.mul_sum] at step1
  linarith

/-- **D4, at `p ≤ R`.** The Artin exponent `a = codim V^I + Sw` of a two-dimensional
representation with `codim V^I ≤ 2` and with every upper group above `U` acting trivially is
at most `2 + 2U`. -/
theorem artin_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (c0 U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc00 : c0 ≤ 2) (hc2 : ∀ i, c i ≤ 2)
    (htriv : ∀ i, U < phi g i → c i = 0) :
    c0 + ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 + 2 * U := by
  have := swan_le g hg0 c U hU n hc2 htriv
  linarith

/-- **D4, tame primes `p > R`.** If the ramification index `e` is less than `p`, the wild
group `G_1` (a `p`-group whose order divides `e`) is trivial. -/
lemma wild_trivial_of_tame {p e k : ℕ} (he : 0 < e) (hep : e < p)
    (hdvd : p ^ k ∣ e) : p ^ k = 1 := by
  rcases k with _ | k
  · simp
  · exfalso
    have := Nat.le_of_dvd he hdvd
    have : p ≤ p ^ (k + 1) := Nat.le_self_pow (by omega) p
    omega

/-- **D4, tame primes**, continued: if `G_1 = 1` then the Swan term vanishes, so the Artin
exponent is `codim V^I ≤ 2`. -/
theorem swan_eq_zero_of_tame (g : ℕ → ℕ) (hanti : Antitone g) (hg1 : g 1 = 1) (c : ℕ → ℚ)
    (hc : ∀ i, g i = 1 → c i = 0) (n : ℕ) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have : g i ≤ 1 := hg1 ▸ hanti hi1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
  · simp [h]
  · simp [hc i h]

/-! ## D2: odd `p`, the character `β` on wild inertia -/

/-- **D2, last sentence.** Let `β : G →* H` be a homomorphism whose values have `p`-power
order, `p` odd (for `G = P_F` pro-`p` and `β` continuous into the finite group `μ_{2m}`, the
image is a finite `p`-group). If `β²` is trivial (`β² = χ` is tame, so trivial on wild
inertia), then `β` is trivial: a pro-`p` group has no quotient of order two (N5 L821-823). -/
theorem char_trivial_of_odd_pgroup {G H : Type*} [Group G] [Group H] (p : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (β : G →* H) (himg : ∀ g, ∃ k : ℕ, β g ^ (p ^ k) = 1)
    (hsq : ∀ g, β g ^ 2 = 1) : ∀ g, β g = 1 := by
  intro g
  obtain ⟨k, h1⟩ := himg g
  have hcop : Nat.Coprime 2 (p ^ k) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have h2 : orderOf (β g) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq g)
  have h3 : orderOf (β g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have : orderOf (β g) ∣ Nat.gcd 2 (p ^ k) := Nat.dvd_gcd h2 h3
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

/-- The image of a homomorphism from a finite `p`-group has `p`-power-order elements, so
`char_trivial_of_odd_pgroup` applies to `β` restricted to any finite `p`-group quotient. -/
lemma pow_card_eq_one_of_pgroup {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (β : G →* H) (g : G) : ∃ k : ℕ, β g ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hG g
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

/-! ## D2-D4: the constants -/

/-- `G₀ = |GL₄(𝔽₅)|` (the degree of `L_v(A[5])/L_v` is at most this). -/
theorem card_GL4_F5 : Nat.card (GL (Fin 4) (ZMod 5)) = 116064000000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 5)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- `|GL₄(𝔽₃)| = 24261120 ≤ G₀` (the degree of `L_v(A[3])/L_v`). -/
theorem card_GL4_F3 : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 3)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- The subgroup-formula threshold at `p = 2`: `max(4D², 3e) ≤ U₀ = 4(D G₀)²` when
`e ≤ D` and `G₀ ≥ 1` (N5 L841-842). -/
theorem max_le_U0 (D G0 e : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) (he : e ≤ D) :
    max (4 * D ^ 2) (3 * e) ≤ 4 * (D * G0) ^ 2 := by
  have h1 : D ^ 2 ≤ (D * G0) ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right D hG) 2
  have h2 : 3 * e ≤ 4 * D ^ 2 := by nlinarith
  omega

/-- `2 + 2U₀ ≤ E₀`, with `U₀ = 4(DG₀)²` and `E₀ = 10(DG₀)²` (N5 L845-846). -/
theorem two_add_two_U0_le_E0 (D G0 : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) :
    2 + 2 * (4 * (D * G0) ^ 2) ≤ 10 * (D * G0) ^ 2 := by
  have : 1 ≤ (D * G0) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hD hG)
  omega


/-! ## D1 over genuine definitions (Mathlib's rings of integers, inertia and different)

For a Galois number field `L/ℚ` and a prime `P` of `𝓞 L`, the lower ramification groups are
`G_i = {σ ∈ Gal(L/ℚ) | ∀ x ∈ 𝓞 L, σ x - x ∈ P^(i+1)}`, i.e. Mathlib's `Ideal.inertia` of
`P^(i+1)`; `G_0` is Mathlib's inertia group. (Serre, *Corps locaux*, IV §1 defines them for the
completion; they agree with these, Serre I §7 and IV §1, UNVERIFIED locators.) The two leaves
below are published theorems (local statements transported to number fields by completion). -/

open NumberField

/-- The lower ramification group `G_i` of `P` in `Gal(L/ℚ)`. -/
abbrev ramGroup (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) :
    Subgroup Gal(L/ℚ) :=
  (P ^ (i + 1)).inertia Gal(L/ℚ)

/-- `|G_i|`. -/
noncomputable abbrev ramCard (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) : ℕ :=
  Nat.card (ramGroup L P i)

/-- **Leaf (Hilbert's different formula; Serre, *Corps locaux*, IV §1, Prop. 4, with `G_i = 1`
for large `i`, IV §1; UNVERIFIED numbering).** For a Galois number field `L` and a nonzero prime
`P` of `𝓞 L`, some `G_n` is trivial and the exact power of `P` in the different of `𝓞 L/ℤ` is
`∑_{i<n} (|G_i| - 1)`. -/
def HilbertDifferentFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- **Leaf (Serre's bound for the different; Serre, *Corps locaux*, III §6, remark after
Prop. 13: `v_L(𝔇_{L/K}) ≤ e - 1 + v_L(e)`; UNVERIFIED numbering).** At `K = ℚ_p`,
`v_L(e) = e·v_p(e)`. Stated for any number field `L` and prime `P | p` of `𝓞 L`. -/
def SerreDifferentBound : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)

instance spanNatPrime_isPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

/-- **D1 over genuine definitions.** From the two leaves: for a Galois number field `L`, a prime
`P | p` with ramification index `e ≤ a!` and a lower index `b` with `G_b ≠ 1`, the upper index
`φ(b)` (Herbrand's function of the genuine `|G_i|`) is at most `4a²`. -/
theorem D1_genuine (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [hPl : P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 := by
  have hp : p.Prime := hpF.out
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set g := ramCard L P with hg_def
  have hanti : Antitone g := by
    intro i j hij
    apply Subgroup.card_le_of_le
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hg1 : ∀ i, 1 ≤ g i := fun i => Nat.card_pos
  have hgb : 2 ≤ g b := by
    have h1 := hg1 b
    have h2 : g b ≠ 1 := fun h => hb (Subgroup.card_eq_one.mp h)
    omega
  obtain ⟨n, hn, hdvd, -⟩ := hH L P hP0
  have hbn : b < n := by
    by_contra h
    apply hb
    rw [eq_bot_iff, ← hn]
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have he : g 0 = P.ramificationIdx ℤ := by
    show Nat.card ((P ^ (0 + 1)).inertia Gal(L/ℚ)) = _
    rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]
  have hSer := hS L p hp P hPl
  have hsum : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0) := by
    rw [he]
    by_contra hlt
    push Not at hlt
    exact hSer (dvd_trans (pow_dvd_pow P hlt) hdvd)
  exact upper_break_le p a hp ha g hanti hg1 b n hgb hbn (he ▸ hea) hsum

end GlueConductor


/-! # glue-d1-local: the local form of D1's degree bound `e ≤ a!`

Glazer bounds only the local degree `[F:ℚ_p] ≤ a` and uses the Galois closure `F̃` of `F/ℚ_p`.
For a finite Galois `L/ℚ` and a prime `P` of `𝓞 L` over `p`, the local Galois group
`Gal(L_P/ℚ_p)` is the decomposition group `D_P = Stab(P) ≤ Gal(L/ℚ)`, and for an intermediate
field `K` with `w = P ∩ 𝓞 K` the subgroup `Gal(L_P/K_w)` is `D_P ∩ Gal(L/K)`
(Serre, *Corps locaux*, II §3, UNVERIFIED locator). So "`L_P` is the Galois closure of
`K_w/ℚ_p`" is the group condition that `D_P ∩ Gal(L/K)` has trivial normal core in `D_P`, and
`[K_w:ℚ_p]` is the index `[D_P : D_P ∩ Gal(L/K)]`. Everything below is stated over Mathlib's
`Gal(L/ℚ)`, `MulAction.stabilizer`, `Ideal.inertia` and `Ideal.ramificationIdx`; no completion
is needed. -/

namespace GlueD1Local

open NumberField GlueConductor
open scoped Pointwise

/-- A subgroup with trivial normal core: the group embeds in the permutations of the cosets,
so `|D| ≤ [D:H]!`. -/
theorem card_le_factorial_index_of_normalCore_eq_bot {D : Type*} [Group D] [Finite D]
    (H : Subgroup D) (hcore : H.normalCore = ⊥) : Nat.card D ≤ H.index.factorial := by
  have h := H.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot] at h
  exact Nat.le_of_dvd (Nat.factorial_pos _) h

/-- Without the core hypothesis: `|D / core_D(H)| ≤ [D:H]!`. -/
theorem index_normalCore_le_factorial_index {D : Type*} [Group D] [Finite D]
    (H : Subgroup D) : H.normalCore.index ≤ H.index.factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) H.index_normalCore_dvd_factorial_index

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

/-- The decomposition group `D_P = Stab(P) ≤ Gal(L/ℚ)`. -/
abbrev decompGroup (P : Ideal (𝓞 L)) : Subgroup Gal(L/ℚ) := MulAction.stabilizer Gal(L/ℚ) P

/-- `Gal(L/K) ∩ D_P`, as a subgroup of `D_P` (the local group `Gal(L_P/K_w)`). -/
abbrev localSub (K : IntermediateField ℚ L) (P : Ideal (𝓞 L)) : Subgroup (decompGroup L P) :=
  K.fixingSubgroup.subgroupOf (decompGroup L P)

/-- `e(P|p) = |I_P| ≤ |D_P|`. -/
theorem ramificationIdx_le_card_decompGroup (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ ≤ Nat.card (decompGroup L P) := by
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (Ideal.span {(p : ℤ)}) P]
  exact Subgroup.card_le_of_le (Ideal.inertia_le_stabilizer P)

/-- **The local degree bound (decomposition-group form).** Let `L/ℚ` be finite Galois, `P` a
prime of `𝓞 L` over `p`, and `K` an intermediate field such that `D_P ∩ Gal(L/K)` has trivial
normal core in `D_P` (i.e. `L_P` is the Galois closure of `K_w` over `ℚ_p`) and index
`[D_P : D_P ∩ Gal(L/K)] ≤ a` (i.e. `[K_w : ℚ_p] ≤ a`). Then `e(P|p) ≤ |D_P| ≤ a!`. -/
theorem ramificationIdx_le_factorial_local (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (hdeg : (localSub L K P).index ≤ a) :
    P.ramificationIdx ℤ ≤ a.factorial :=
  (ramificationIdx_le_card_decompGroup L p P).trans
    ((card_le_factorial_index_of_normalCore_eq_bot _ hcore).trans (Nat.factorial_le hdeg))

/-- **D1, local form.** The hypothesis `e ≤ a!` of `D1_genuine` is replaced by the local data:
`L_P` is the Galois closure of `K_w/ℚ_p` and `[K_w:ℚ_p] ≤ a`. -/
theorem D1_local (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : (localSub L K P).index ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine hH hS L p P a ha (ramificationIdx_le_factorial_local L p P K hcore a hdeg) b hb

/-- `|D_P| = e(P|p)·f(P|p)` (Mathlib's `Ideal.card_stabilizer_eq`). -/
theorem card_decompGroup (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (decompGroup L P) = P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  rw [Ideal.card_stabilizer_eq (G := Gal(L/ℚ)) (Ideal.span {(p : ℤ)}) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]

/-- `D_P ∩ Gal(L/K)` is the stabilizer of `P` in `Gal(L/K)`. -/
def localSubEquiv (K : IntermediateField ℚ L) (P : Ideal (𝓞 L)) :
    localSub L K P ≃ MulAction.stabilizer K.fixingSubgroup P where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The local degree as an index.** For `w = P ∩ 𝓞 K`,
`[D_P : D_P ∩ Gal(L/K)] = e(w|p)·f(w|p)` (the local degree `[K_w : ℚ_p]`). -/
theorem index_localSub (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) :
    (localSub L K P).index =
      (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ := by
  have hD := card_decompGroup L p P
  have : IsGaloisGroup K.fixingSubgroup K L :=
    IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K
  have : IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ (𝓞 K) (𝓞 L) K L
  have hH : Nat.card (MulAction.stabilizer K.fixingSubgroup P) =
      P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    have h1 := Ideal.card_stabilizer_eq (G := K.fixingSubgroup) (P.under (𝓞 K)) P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P K.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 K)) P K.fixingSubgroup] at h1
    exact h1
  have hS : Nat.card (localSub L K P) = P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    rw [← hH]; exact Nat.card_congr (localSubEquiv L K P)
  have he := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 K)) P
  have hf := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 K)) P
  have hmul := (localSub L K P).card_mul_index
  rw [hS, hD, he, hf] at hmul
  have hpos : 0 < P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    rw [← hS]; exact Nat.card_pos
  have : P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) * (localSub L K P).index =
      P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) *
        ((P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ) := by
    rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

/-- **D1, local form, with the local degree as `e(w|p)·f(w|p)`.** -/
theorem D1_local' (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_local L hH hS p P K hcore a ha ((index_localSub L p P K).trans_le hdeg) b hb

/-! ## The Krasner-type situation: `K` has a single prime over `p`

If `L` is the Galois closure of `K` over `ℚ` (`core_G(Gal(L/K)) = ⊥`) and `K` has only one prime
`w` over `p`, then the core hypothesis of `D1_local'` holds: `L_P` is then the Galois closure of
`K_w`. Krasner's lemma gives such a `K` for any finite `F/ℚ_p` (`K = ℚ(α)` with the minimal
polynomial of `α` close to that of a generator of `F`; then `K_w ≅ F` and `[K:ℚ] = [F:ℚ_p]`). -/

/-- Group theory: if `G = H·D` and `core_G(H) = ⊥`, then `core_D(H ∩ D) = ⊥`. -/
theorem normalCore_subgroupOf_eq_bot {G : Type*} [Group G] (D H : Subgroup G)
    (hHD : ∀ g : G, ∃ h ∈ H, ∃ d ∈ D, g = h * d) (hcore : H.normalCore = ⊥) :
    (H.subgroupOf D).normalCore = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx : ∀ b : D, b * x * b⁻¹ ∈ H.subgroupOf D := hx
  have hxG : (x : G) ∈ H.normalCore := by
    show ∀ g : G, g * x * g⁻¹ ∈ H
    intro g
    obtain ⟨h, hh, d, hd, rfl⟩ := hHD g
    have h1 := hx ⟨d, hd⟩
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : h * (d * x * d⁻¹) * h⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hh (by simpa using h1)) (H.inv_mem hh)
    simpa [mul_assoc] using h2
  rw [hcore, Subgroup.mem_bot] at hxG
  exact (Subgroup.mem_bot).mpr (Subtype.ext hxG)

/-- If `K` has a single prime `w` over `p`, then `Gal(L/ℚ) = Gal(L/K)·D_P`. -/
theorem fixingSubgroup_mul_decompGroup (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K)) (g : Gal(L/ℚ)) :
    ∃ h ∈ K.fixingSubgroup, ∃ d ∈ decompGroup L P, g = h * d := by
  have : IsGaloisGroup K.fixingSubgroup K L :=
    IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K
  have : IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ (𝓞 K) (𝓞 L) K L
  have hQ : (g • P).IsPrime := Ideal.IsPrime.smul g
  have hv : (g • P).under (𝓞 K) = P.under (𝓞 K) := by
    apply hunique _ (Ideal.IsPrime.under _ _)
    refine ⟨?_⟩
    have h1 : (g • P).under ℤ = Ideal.span {(p : ℤ)} := by
      rw [Ideal.under_smul, ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
    rw [← h1, Ideal.under_under]
  obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) K.fixingSubgroup
    P (g • P) hv.symm
  refine ⟨h, h.2, h⁻¹ * g, ?_, by simp⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, hh]
  exact inv_smul_smul (h : Gal(L/ℚ)) P

/-- **The Krasner-type form.** If `L` is the Galois closure of `K` (`core_G(Gal(L/K)) = ⊥`), `K`
has a single prime `w` over `p`, and `e(w|p)·f(w|p) ≤ a`, then `e(P|p) ≤ a!`. -/
theorem ramificationIdx_le_factorial_of_unique (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a) :
    P.ramificationIdx ℤ ≤ a.factorial :=
  ramificationIdx_le_factorial_local L p P K
    (normalCore_subgroupOf_eq_bot _ _ (fixingSubgroup_mul_decompGroup L p P K hunique) hclos)
    a ((index_localSub L p P K).trans_le hdeg)

/-- **D1 in the Krasner-type situation.** -/
theorem D1_krasner (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine hH hS L p P a ha (ramificationIdx_le_factorial_of_unique L p P K hclos hunique a hdeg)
    b hb

/-- Galois correspondence: if `L` is the normal closure of `K` over `ℚ`, then
`core_G(Gal(L/K)) = ⊥`. -/
theorem normalCore_fixingSubgroup_eq_bot (K : IntermediateField ℚ L)
    (h : IntermediateField.normalClosure ℚ K L = ⊤) : K.fixingSubgroup.normalCore = ⊥ := by
  set N := K.fixingSubgroup.normalCore
  have : N.Normal := Subgroup.normalCore_normal _
  have hK : K ≤ IntermediateField.fixedField N := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff K σ).mp
      (Subgroup.normalCore_le _ hσ) x hx
  have htop : IntermediateField.fixedField N = ⊤ := by
    rw [eq_top_iff, ← h]
    exact (IntermediateField.normalClosure_le_iff_of_normal).mpr hK
  rw [← IntermediateField.fixingSubgroup_fixedField N, htop, IntermediateField.fixingSubgroup_top]

/-- `D1_krasner` with "`L` is the normal closure of `K`" as a field-theoretic hypothesis. -/
theorem D1_krasner' (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : IntermediateField.normalClosure ℚ K L = ⊤)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_krasner L hH hS p P K (normalCore_fixingSubgroup_eq_bot L K hclos) hunique a ha hdeg b hb

end GlueD1Local

#print axioms GlueD1Local.ramificationIdx_le_factorial_local
#print axioms GlueD1Local.D1_local
#print axioms GlueD1Local.index_localSub
#print axioms GlueD1Local.D1_local'
#print axioms GlueD1Local.ramificationIdx_le_factorial_of_unique
#print axioms GlueD1Local.D1_krasner
#print axioms GlueD1Local.D1_krasner'
