import ZInQKernel.Size.Norms.Quadratic
import ZInQKernel.Size.Norms.DivisionPolynomials
import ZInQKernel.Model.DivisionPolynomials.FixedPointCodes
import ZInQKernel.Model.DivisionPolynomials.Components
import ZInQKernel.Model.Generator.InfiniteOrder

/-!
# Heights of the codes in the guard box

Blueprint: `size/norms/coordinate-heights.md`.

For `|n| ≤ T` every coordinate of `ι(n)` has reduced numerator and denominator at most `2^K`,
`K = 2^30 (T + 1)³` (`iota_coord_height`). For `|m| ≤ 2T` the value `ψ_m(P₀)` is represented by
the triple `(32^δ Ψ_{m,0}(P₀), 32^δ Ψ_{m,1}(P₀), 32^δ)`, `δ = 2(|m| + 1)³`, of size at most
`2^{135 (|m|+1)³} ≤ 2^{1080 (T+1)³}` (`exists_int_eval`, `rep_psiP0`); four levels of field
operations, each taking a size `2^h` to `3 · 2^{4h} ≤ 2^{8h}`, give `x([n]P₀)` and `y([n]P₀)`.
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 psiComponent psiComponent_eval psiEval)

/-! ### Clearing denominators in an evaluation -/

/-- If `P` has degree at most `δ`, then `q^δ P(w/q)` is an integer of absolute value at most
`‖P‖₁ V^δ`, provided `|w_i| ≤ V` and `q ≤ V`. -/
theorem exists_int_eval {σ : Type*} (P : MvPolynomial σ ℤ) (w : σ → ℤ) {q V δ : ℕ} (hq : 0 < q)
    (hqV : q ≤ V) (hw : ∀ i, (w i).natAbs ≤ V) (hδ : P.totalDegree ≤ δ) :
    ∃ a : ℤ, (q : ℚ) ^ δ * eval₂ (Int.castRingHom ℚ) (fun i => (w i : ℚ) / q) P = a ∧
      a.natAbs ≤ l1 P * V ^ δ := by
  classical
  set t : (σ →₀ ℕ) → ℤ := fun α =>
    P.coeff α * (∏ i ∈ α.support, w i ^ α i) * (q : ℤ) ^ (δ - ∑ i ∈ α.support, α i) with ht
  refine ⟨∑ α ∈ P.support, t α, ?_, ?_⟩
  · conv_lhs => rw [P.as_sum]
    rw [eval₂_sum, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun α hα => ?_
    have hle : (∑ i ∈ α.support, α i) ≤ δ := (le_totalDegree hα).trans hδ
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [eval₂_monomial, Finsupp.prod]
    simp only [ht, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast]
    push_cast
    conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add]
    field_simp
  · have hV : (0 : ℤ) ≤ V := by positivity
    have habs : ∀ α ∈ P.support, |t α| ≤ |P.coeff α| * (V : ℤ) ^ δ := by
      intro α hα
      have hle : (∑ i ∈ α.support, α i) ≤ δ := (le_totalDegree hα).trans hδ
      simp only [ht, abs_mul, abs_pow, Finset.abs_prod, Nat.abs_cast]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h1 : ∏ i ∈ α.support, |w i| ^ α i ≤ (V : ℤ) ^ ∑ i ∈ α.support, α i := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        rw [Int.abs_eq_natAbs]; exact_mod_cast hw i
      have h2 : (q : ℤ) ^ (δ - ∑ i ∈ α.support, α i) ≤ (V : ℤ) ^ (δ - ∑ i ∈ α.support, α i) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqV) _
      calc (∏ i ∈ α.support, |w i| ^ α i) * (q : ℤ) ^ (δ - ∑ i ∈ α.support, α i)
          ≤ (V : ℤ) ^ (∑ i ∈ α.support, α i) * (V : ℤ) ^ (δ - ∑ i ∈ α.support, α i) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (V : ℤ) ^ δ := by rw [← pow_add, Nat.add_sub_cancel' hle]
    have hsum : |∑ α ∈ P.support, t α| ≤ (l1 P : ℤ) * (V : ℤ) ^ δ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum habs).trans (le_of_eq ?_))
      rw [← Finset.sum_mul, Syntax.l1, Nat.cast_sum]
      simp only [Int.natCast_natAbs]
    rw [Int.abs_eq_natAbs] at hsum
    exact_mod_cast hsum

/-! ### Represented elements of `K₀` -/

/-- `u ∈ K₀` is represented by a triple of size at most `2^h`. -/
def Rep (u : K0) (h : ℕ) : Prop := ∃ r : QRep, r.val = u ∧ r.size ≤ 2 ^ h

namespace Rep

variable {u v : K0} {h : ℕ}

theorem mono (hu : Rep u h) {h' : ℕ} (hh : h ≤ h') : Rep u h' := by
  obtain ⟨r, hr, hs⟩ := hu
  exact ⟨r, hr, hs.trans (Nat.pow_le_pow_right (by norm_num) hh)⟩

private theorem level (hh : 1 ≤ h) : 3 * (2 ^ h) ^ 4 ≤ 2 ^ (8 * h) := by
  rw [← pow_mul]
  calc 3 * 2 ^ (h * 4) ≤ 2 ^ 2 * 2 ^ (h * 4) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (2 + h * 4) := (pow_add 2 2 _).symm
    _ ≤ 2 ^ (8 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem two_le (hh : 1 ≤ h) : 2 ≤ 2 ^ h :=
  (Nat.pow_le_pow_right (by norm_num) hh : 2 ^ 1 ≤ 2 ^ h)

theorem add (hh : 1 ≤ h) (hu : Rep u h) (hv : Rep v h) : Rep (u + v) (8 * h) := by
  obtain ⟨r, rfl, hr⟩ := hu; obtain ⟨r', rfl, hr'⟩ := hv
  obtain ⟨q, hq, hs⟩ := QRep.exists_add r r' (two_le hh) hr hr'
  exact ⟨q, hq, hs.trans (level hh)⟩

theorem sub (hh : 1 ≤ h) (hu : Rep u h) (hv : Rep v h) : Rep (u - v) (8 * h) := by
  obtain ⟨r, rfl, hr⟩ := hu; obtain ⟨r', rfl, hr'⟩ := hv
  obtain ⟨q, hq, hs⟩ := QRep.exists_sub r r' (two_le hh) hr hr'
  exact ⟨q, hq, hs.trans (level hh)⟩

theorem mul (hh : 1 ≤ h) (hu : Rep u h) (hv : Rep v h) : Rep (u * v) (8 * h) := by
  obtain ⟨r, rfl, hr⟩ := hu; obtain ⟨r', rfl, hr'⟩ := hv
  obtain ⟨q, hq, hs⟩ := QRep.exists_mul r r' (two_le hh) hr hr'
  exact ⟨q, hq, hs.trans (level hh)⟩

theorem two_mul (hh : 1 ≤ h) (hu : Rep u h) : Rep (2 * u) (8 * h) := by
  obtain ⟨r, rfl, hr⟩ := hu
  obtain ⟨q, hq, hs⟩ := QRep.exists_two_mul r (two_le hh) hr
  exact ⟨q, hq, hs.trans (level hh)⟩

theorem div (hh : 1 ≤ h) (hu : Rep u h) (hv : Rep v h) (h0 : v ≠ 0) : Rep (u / v) (8 * h) := by
  obtain ⟨r, rfl, hr⟩ := hu; obtain ⟨r', rfl, hr'⟩ := hv
  obtain ⟨q, hq, hs⟩ := QRep.exists_div r r' (two_le hh) hr hr' h0
  exact ⟨q, hq, hs.trans (level hh)⟩

/-- The rational coordinates of a represented element have reduced numerators and denominators
at most `2^K` for `h ≤ K`. -/
theorem coords (hu : Rep u h) {K : ℕ} (hK : h ≤ K) :
    (u.re.num.natAbs ≤ 2 ^ K ∧ u.re.den ≤ 2 ^ K) ∧ (u.im.num.natAbs ≤ 2 ^ K ∧ u.im.den ≤ 2 ^ K) := by
  obtain ⟨r, rfl, hr⟩ := hu
  have hr' := hr.trans (Nat.pow_le_pow_right (by norm_num) hK)
  obtain ⟨-, -, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := QRep.coord_bounds r
  exact ⟨⟨h1.trans hr', h2.trans hr'⟩, ⟨h3.trans hr', h4.trans hr'⟩⟩

end Rep

/-! ### The values `ψ_m(P₀)` -/

/-- The coordinates of `P₀` over the denominator `32`: `x₀ = 6564/32`, `x₁ = -4640/32`,
`y₀ = -123720/32`, `y₁ = 87483/32`. -/
def p0Num : Fin 4 → ℤ := ![6564, -4640, -123720, 87483]

theorem p0Num_natAbs_le (i : Fin 4) : (p0Num i).natAbs ≤ 2 ^ 17 := by
  fin_cases i <;> decide

theorem genX0_eq_p0Num : genX0 = ⟨(p0Num 0 : ℚ) / 32, (p0Num 1 : ℚ) / 32⟩ := by
  ext <;> norm_num [genX0, p0Num]

theorem genY0_eq_p0Num : genY0 = ⟨(p0Num 2 : ℚ) / 32, (p0Num 3 : ℚ) / 32⟩ := by
  ext <;> norm_num [genY0, p0Num]

/-- The components of `ψ_k(P₀)` are the component polynomials evaluated at `P₀`. -/
theorem psiP0_coord (k : ℤ) (c : Fin 2) :
    ![(psiP0 k).re, (psiP0 k).im] c =
      eval₂ (Int.castRingHom ℚ) (fun i => (p0Num i : ℚ) / 32) (psiComponent k c) := by
  rw [psiComponent_eval, psiP0, genX0_eq_p0Num, genY0_eq_p0Num]

/-- `ψ_k(P₀)` is represented by a triple of size at most `2^{135 (|k|+1)³}`. -/
theorem rep_psiP0 (k : ℤ) : Rep (psiP0 k) (135 * (k.natAbs + 1) ^ 3) := by
  set K := (k.natAbs + 1) ^ 3 with hK
  set δ := 2 * K with hδ
  have hV : ∀ c : Fin 2, l1 (psiComponent k c) * (2 ^ 17) ^ δ ≤ 2 ^ (135 * K) := by
    intro c
    have := (ZInQ.Size.psiComponent_size k c).2
    rw [← pow_mul, show 135 * K = 101 * K + 17 * δ by omega, pow_add]
    exact Nat.mul_le_mul_right _ this
  obtain ⟨a, ha, ha'⟩ := exists_int_eval (psiComponent k 0) p0Num (q := 32) (V := 2 ^ 17)
    (δ := δ) (by norm_num) (by norm_num) p0Num_natAbs_le (ZInQ.Size.psiComponent_size k 0).1
  obtain ⟨b, hb, hb'⟩ := exists_int_eval (psiComponent k 1) p0Num (q := 32) (V := 2 ^ 17)
    (δ := δ) (by norm_num) (by norm_num) p0Num_natAbs_le (ZInQ.Size.psiComponent_size k 1).1
  have h0 := psiP0_coord k 0
  have h1 := psiP0_coord k 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have h32 : ((32 : ℕ) : ℚ) ^ δ ≠ 0 := by positivity
  refine ⟨⟨a, b, 32 ^ δ, by positivity⟩, ?_, ?_⟩
  · ext
    · simp only [QRep.val]; push_cast at ha ⊢; rw [h0, ← ha]; field_simp
    · simp only [QRep.val]; push_cast at hb ⊢; rw [h1, ← hb]; field_simp
  · simp only [QRep.size, max_le_iff]
    refine ⟨ha'.trans (hV 0), hb'.trans (hV 1), ?_⟩
    rw [Int.natAbs_pow, show (32 : ℤ).natAbs = 2 ^ 5 by rfl, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `x(P₀) = (1641 - 1160 s)/8`. -/
theorem rep_genX0 {h : ℕ} (hh : 11 ≤ h) : Rep genX0 h := by
  refine ⟨⟨1641, -1160, 8, by norm_num⟩, ?_, ?_⟩
  · ext <;> norm_num [QRep.val, genX0]
  · refine le_trans ?_ (Nat.pow_le_pow_right (by norm_num) hh)
    decide

/-! ### The codes -/

/-- For `1 ≤ n ≤ T`, `x([n]P₀)` and `y([n]P₀)` are represented by triples of size at most
`2^{2^9 h₀}` and `2^{2^12 h₀}`, `h₀ = 1080 (T+1)³`. -/
theorem rep_fixed (T n : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) :
    Rep (fixedX n) (512 * (1080 * (T + 1) ^ 3)) ∧ Rep (fixedY n) (4096 * (1080 * (T + 1) ^ 3)) := by
  set h₀ := 1080 * (T + 1) ^ 3 with hh₀
  have hT1 : 1 ≤ (T + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hh : 1 ≤ h₀ := by omega
  have hpsi : ∀ k : ℤ, k.natAbs ≤ 2 * T → Rep (psiP0 k) h₀ := by
    intro k hk
    refine (rep_psiP0 k).mono ?_
    have : (k.natAbs + 1) ^ 3 ≤ 8 * (T + 1) ^ 3 := by
      calc (k.natAbs + 1) ^ 3 ≤ (2 * (T + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 8 * (T + 1) ^ 3 := by ring
    omega
  have hn0 : psiP0 n ≠ 0 := ((iota_eq_psi genP0_not_isOfFinAddOrder).1 n (by exact_mod_cast hn)).1
  have hp := hpsi (n + 1) (by omega)
  have hm := hpsi (n - 1) (by omega)
  have hc := hpsi n (by omega)
  have h2n := hpsi (2 * n) (by omega)
  have hsq : Rep (psiP0 n ^ 2) (8 * h₀) := by rw [pow_two]; exact hc.mul hh hc
  have hsq0 : psiP0 n ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  constructor
  · have hq := (hp.mul hh hm).div (by omega) hsq hsq0
    have := ((rep_genX0 (h := 8 * (8 * h₀)) (by omega)).sub (by omega) hq)
    rw [fixedX]
    exact this.mono (by omega)
  · have h4 : Rep (psiP0 n ^ 4) (8 * (8 * h₀)) := by
      rw [show psiP0 n ^ 4 = psiP0 n ^ 2 * psiP0 n ^ 2 by ring]
      exact hsq.mul (by omega) hsq
    have h24 := h4.two_mul (by omega)
    have h240 : 2 * psiP0 n ^ 4 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 4 hn0)
    have := (h2n.mono (h' := 8 * (8 * (8 * h₀))) (by omega)).div (by omega) h24 h240
    rw [fixedY]
    exact this.mono (by omega)

private theorem num_den_neg_le {q : ℚ} {N : ℕ} (h : q.num.natAbs ≤ N ∧ q.den ≤ N) :
    (-q).num.natAbs ≤ N ∧ (-q).den ≤ N := by
  rwa [Rat.num_neg_eq_neg_num, Int.natAbs_neg, Rat.den_neg_eq_den]

/-- **Heights of the codes in the guard box.** For `|n| ≤ T` and `K = 2^30 (T + 1)³`, each of
the five coordinates of `ι(n)` has reduced numerator of absolute value at most `2^K` and
positive reduced denominator at most `2^K`. -/
theorem iota_coord_height (T : ℕ) (n : ℤ) (hn : n.natAbs ≤ T) (i : Fin 5) :
    ((iota n) i).num.natAbs ≤ 2 ^ (2 ^ 30 * (T + 1) ^ 3) ∧
      ((iota n) i).den ≤ 2 ^ (2 ^ 30 * (T + 1) ^ 3) := by
  set K := 2 ^ 30 * (T + 1) ^ 3
  have h1K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hcodes := iota_eq_psi genP0_not_isOfFinAddOrder
  rcases lt_trichotomy n 0 with hlt | rfl | hgt
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    have hm : 1 ≤ m := by omega
    have hmT : m ≤ T := by omega
    obtain ⟨hX, hY⟩ := rep_fixed T m hm hmT
    obtain ⟨hXr, hXi⟩ := hX.coords (K := K) (by omega)
    obtain ⟨hYr, hYi⟩ := hY.coords (K := K) (by omega)
    rw [(hcodes.1 m (by exact_mod_cast hm)).2.2]
    fin_cases i
    · simp [h1K]
    · exact hXr
    · exact hXi
    · exact num_den_neg_le hYr
    · exact num_den_neg_le hYi
  · rw [hcodes.2]
    fin_cases i <;> simp [h1K]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.natAbs, by omega⟩
    have hm : 1 ≤ m := by omega
    have hmT : m ≤ T := by omega
    obtain ⟨hX, hY⟩ := rep_fixed T m hm hmT
    obtain ⟨hXr, hXi⟩ := hX.coords (K := K) (by omega)
    obtain ⟨hYr, hYi⟩ := hY.coords (K := K) (by omega)
    rw [(hcodes.1 m (by exact_mod_cast hm)).2.1]
    fin_cases i
    · simp [h1K]
    · exact hXr
    · exact hXi
    · exact hYr
    · exact hYi

end ZInQ.Size
