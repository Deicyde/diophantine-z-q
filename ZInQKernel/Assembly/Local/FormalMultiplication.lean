import ZInQKernel.Multiplication.Local

/-!
# Multiplication in a formal neighbourhood

Blueprint: `assembly/local-tests/formal-multiplication.md`.

Let `K` be a field, `v : AddValuation K (WithTop ℤ)` and `A ∈ K` with `v(A) ≥ 0`;
`W_k(K) = formalFilt A hA k` and `z = -x/y` (`ZInQ.Mult.zCoord`). Then:

1. for `k ≥ 1` and `P, Q ∈ W_k(K)`, `v(z(P + Q) - z(P) - z(Q)) ≥ 5k` (`val_zCoord_add_sub`);
2. for affine `Q ∈ W₁(K)` with `k = v(z(Q))` and `n ∈ ℤ`, `v(z([n]Q) - n z(Q)) ≥ 5k` and
   `v(z([n]Q)/z(Q) - n) ≥ 4k` (`val_zCoord_zsmul_sub`);
3. if `v(p) ≥ 1` then `[p]W_k(K) ⊆ W_{k+1}(K)` (`zsmul_mem_formalFilt_succ`); if `v(p) = e ≤ 4`
   then `[n]W_k(K) ⊆ W_{k + e v_p(n)}(K)` for `n ≠ 0` (`zsmul_mem_formalFilt_add_val`), and
   `e v_p(n) = v(n)` when the residue characteristic is `p` (`v(m) = 0` for `p ∤ m`;
   `val_intCast_eq`);
4. if `v(p) = 1` and the residue characteristic is `p`, then for affine `Q ∈ W₁(K)` with
   `k = v(z(Q))` and `m ≠ 0`, `[m]Q` is affine, `v(z([m]Q)) = k + v_p(m)` and
   `z([m]Q) = m z(Q) u` with `v(u - 1) ≥ 1` (`zCoord_zsmul_eq_mul_unit`).

On `K₀`, `Ek π hπ k` is the subgroup `E_k(π)` of `E(K₀)` at the valuation `v_π`; the hypotheses
of items 3 and 4 hold at every prime above an odd prime `p` (with `e = 1`) and item 3 at `(s)`
(with `e = 2`).

The article assumes characteristic `0`, a normalized valuation and a residue field of
characteristic `p`; the statements here use only the valuation facts listed, and item 4 does not
need `p` odd.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult

section General

variable {K : Type*} [Field K] [DecidableEq K] {v : AddValuation K (WithTop ℤ)} {A : K}

omit [DecidableEq K] in
theorem ne_zero_of_val_zCoord {P : (shortCurve A).toAffine.Point} {k : ℤ}
    (hk : v (Mult.zCoord P) = k) : P ≠ 0 := by
  rintro rfl
  rw [zCoord_zero, v.map_zero] at hk
  exact WithTop.top_ne_coe hk

variable (hA : 0 ≤ v A)
include hA

/-- **Item 1.** `z` is additive on `W_k(K)` modulo valuation `5k`. -/
theorem val_zCoord_add_sub {k : ℤ} (hk : 1 ≤ k) {P Q : (shortCurve A).toAffine.Point}
    (hP : P ∈ formalFilt A hA k) (hQ : Q ∈ formalFilt A hA k) :
    Vge v (5 * k) (Mult.zCoord (P + Q) - Mult.zCoord P - Mult.zCoord Q) := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [point_zero_eq, zero_add, zCoord_zero, sub_zero, sub_self]; exact Vge.zero _
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [point_zero_eq, add_zero, zCoord_zero, sub_zero, sub_self]; exact Vge.zero _
  by_cases hs : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0
  · have hQ' : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ := eq_neg_of_add_eq_zero_right hs
    rw [hs, hQ', zCoord_neg, zCoord_zero]
    convert Vge.zero (v := v) (5 * k) using 1; ring
  obtain ⟨N₁, -, hy₁, ht₁, hw₁, hz₁⟩ := level_of_mem_W1 hA h₁ hP.1
  obtain ⟨N₂, -, hy₂, ht₂, hw₂, hz₂⟩ := level_of_mem_W1 hA h₂ hQ.1
  have hk₁ : k ≤ N₁ := by have := hP.2; rw [hz₁] at this; exact_mod_cast this
  have hk₂ : k ≤ N₂ := by have := hQ.2; rw [hz₂] at this; exact_mod_cast this
  obtain ⟨x₃, y₃, h₃, heq, -, -, -, -, -, -, -, -, -, -, h5⟩ := chord_add_five (v := v) hA hk h₁ h₂
    hy₁ hy₂ ((vge_iff_of_eq ht₁).mpr hk₁) ((vge_iff_of_eq ht₂).mpr hk₂)
    ((vge_iff_of_eq hw₁).mpr (by omega)) ((vge_iff_of_eq hw₂).mpr (by omega)) hs
  rw [heq, zCoord_some, zCoord_some, zCoord_some]
  have := h5.neg
  convert this using 1
  ring

/-- Item 2 for natural multiples of a point of `W_k(K)`. -/
theorem val_zCoord_nsmul_sub {k : ℤ} (hk : 1 ≤ k) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) (n : ℕ) :
    Vge v (5 * k) (Mult.zCoord (n • Q) - n * Mult.zCoord Q) := by
  induction n with
  | zero => rw [zero_smul, zCoord_zero, Nat.cast_zero, zero_mul, sub_zero]; exact Vge.zero _
  | succ j ih =>
    have hj : j • Q ∈ formalFilt A hA k := (formalFilt A hA k).nsmul_mem hQ j
    have := (val_zCoord_add_sub hA hk hj hQ).add ih
    rw [succ_nsmul]
    convert this using 1
    push_cast; ring

/-- Item 2 for integer multiples of a point of `W_k(K)`. -/
theorem val_zCoord_zsmul_sub_of_mem {k : ℤ} (hk : 1 ≤ k) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) (n : ℤ) :
    Vge v (5 * k) (Mult.zCoord (n • Q) - n * Mult.zCoord Q) := by
  rcases Int.eq_nat_or_neg n with ⟨j, rfl | rfl⟩
  · rw [natCast_zsmul, Int.cast_natCast]; exact val_zCoord_nsmul_sub hA hk hQ j
  · rw [neg_smul, natCast_zsmul, zCoord_neg, Int.cast_neg, Int.cast_natCast]
    have := (val_zCoord_nsmul_sub hA hk hQ j).neg
    convert this using 1
    ring

/-- **Item 2.** For an affine `Q ∈ W₁(K)` with `v(z(Q)) = k` and every `n ∈ ℤ`,
`v(z([n]Q) - n z(Q)) ≥ 5k` and `v(z([n]Q)/z(Q) - n) ≥ 4k`. -/
theorem val_zCoord_zsmul_sub {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ W1 v A) {k : ℤ}
    (hk : v (Mult.zCoord Q) = k) (n : ℤ) :
    Vge v (5 * k) (Mult.zCoord (n • Q) - n * Mult.zCoord Q) ∧
      Vge v (4 * k) (Mult.zCoord (n • Q) / Mult.zCoord Q - n) := by
  have hk1 : 1 ≤ k := by
    have := one_le_val_zCoord hA hQ; rw [hk] at this; exact_mod_cast this
  have hQk : Q ∈ formalFilt A hA k := ⟨hQ, by rw [hk]⟩
  have h5 := val_zCoord_zsmul_sub_of_mem hA hk1 hQk n
  refine ⟨h5, ?_⟩
  have hz0 : Mult.zCoord Q ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hk; exact WithTop.top_ne_coe hk
  have := h5.div_val' hk
  rw [sub_div, mul_div_assoc, div_self hz0, mul_one] at this
  exact this.mono (by omega)

/-- The core of item 3: `[n]W_k(K) ⊆ W_{k + min(e, 4k)}(K)` when `v(n) ≥ e ≥ 0`. -/
theorem zsmul_mem_formalFilt_of_vge {k : ℤ} {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) {n : ℤ} {e : ℤ} (hn : Vge v e (n : K)) :
    n • Q ∈ formalFilt A hA (k + min e (4 * k)) := by
  refine ⟨((formalFilt A hA k).zsmul_mem hQ n).1, ?_⟩
  rcases Q with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, zsmul_zero, zCoord_zero, v.map_zero]; exact le_top
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA h hQ.1
  have hkN : k ≤ N := by have := hQ.2; rw [hz] at this; exact_mod_cast this
  have hQN : Point.some x y h ∈ formalFilt A hA N := ⟨hQ.1, by rw [hz]⟩
  have h5 := val_zCoord_zsmul_sub_of_mem hA hN hQN n
  have h1 : Vge v (e + N) ((n : K) * Mult.zCoord (Point.some x y h)) := hn.mul (Vge.of_eq hz)
  have hsum := (h5.mono (show k + min e (4 * k) ≤ 5 * N by omega)).add
    (h1.mono (show k + min e (4 * k) ≤ e + N by omega))
  rw [sub_add_cancel] at hsum
  exact hsum

/-- **Item 3, first part.** If `v(p) ≥ 1` then `[p]W_k(K) ⊆ W_{k+1}(K)` for `k ≥ 1`. -/
theorem zsmul_mem_formalFilt_succ {p : ℤ} (hp : Vge v 1 (p : K)) {k : ℤ} (hk : 1 ≤ k)
    {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ formalFilt A hA k) :
    p • Q ∈ formalFilt A hA (k + 1) :=
  formalFilt_antitone hA (by omega) (zsmul_mem_formalFilt_of_vge hA hQ hp)

omit hA [DecidableEq K] in
/-- With residue characteristic `p` (`v(p) = e` and `v(m) = 0` for `p ∤ m`),
`v(n) = e v_p(n)` for `n ≠ 0`. -/
theorem val_intCast_eq {p : ℕ} [Fact p.Prime] {e : ℤ} (hpe : v (p : K) = e)
    (hres : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → v (m : K) = 0) {n : ℤ} (hn : n ≠ 0) :
    v (n : K) = (e * padicValInt p n : ℤ) := by
  induction h : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ N ih =>
    by_cases hpn : (p : ℤ) ∣ n
    · obtain ⟨n₁, rfl⟩ := hpn
      have hn₁ : n₁ ≠ 0 := by rintro rfl; simp at hn
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have hlt : n₁.natAbs < N := by
        rw [← h, Int.natAbs_mul]
        have := (Fact.out : p.Prime).one_lt
        have : 0 < n₁.natAbs := Int.natAbs_pos.mpr hn₁
        simp only [Int.natAbs_natCast]; nlinarith
      rw [Int.cast_mul, v.map_mul, Int.cast_natCast, hpe, ih _ hlt hn₁ rfl,
        padicValInt.mul hp0 hn₁, padicValInt_self, ← WithTop.coe_add]
      congr 1; push_cast; ring
    · rw [hres n hpn, padicValInt.eq_zero_of_not_dvd hpn]; simp

/-- **Item 3, second part.** If `v(p) = e ≤ 4`, then `[n]W_k(K) ⊆ W_{k + e v_p(n)}(K)` for
`n ≠ 0` and `k ≥ 1`; with residue characteristic `p`, `e v_p(n) = v(n)` (`val_intCast_eq`). -/
theorem zsmul_mem_formalFilt_add_val {p : ℕ} [Fact p.Prime] {e : ℤ} (hpe : v (p : K) = e)
    (he : e ≤ 4) {n : ℤ} (hn : n ≠ 0) {k : ℤ}
    (hk : 1 ≤ k) {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ formalFilt A hA k) :
    n • Q ∈ formalFilt A hA (k + e * padicValInt p n) := by
  have he0 : 0 ≤ e := by
    have h1 : (0 : WithTop ℤ) ≤ v (p : K) := by
      have := Mult.vge_natCast (v := v) p; exact this
    rw [hpe] at h1; exact_mod_cast h1
  induction h : n.natAbs using Nat.strong_induction_on generalizing n k Q with
  | _ N ih =>
    by_cases hpn : (p : ℤ) ∣ n
    · obtain ⟨n₁, rfl⟩ := hpn
      have hn₁ : n₁ ≠ 0 := by rintro rfl; simp at hn
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have hlt : n₁.natAbs < N := by
        rw [← h, Int.natAbs_mul]
        have := (Fact.out : p.Prime).one_lt
        have : 0 < n₁.natAbs := Int.natAbs_pos.mpr hn₁
        simp only [Int.natAbs_natCast]; nlinarith
      have hpQ : (p : ℤ) • Q ∈ formalFilt A hA (k + e) := by
        have := zsmul_mem_formalFilt_of_vge hA hQ (n := p) (e := e)
          (by rw [Int.cast_natCast]; exact Vge.of_eq hpe)
        rwa [min_eq_left (by omega)] at this
      have := ih _ hlt hn₁ (by omega) hpQ rfl
      rw [show (p : ℤ) * n₁ = n₁ * p from mul_comm _ _, mul_smul, padicValInt.mul hn₁ hp0,
        padicValInt_self]
      convert this using 2
      push_cast; ring
    · rw [padicValInt.eq_zero_of_not_dvd hpn]
      simpa using (formalFilt A hA k).zsmul_mem hQ n

/-- The step of item 4: if `v(n) = c ≤ 4k - 1` for an affine `Q ∈ W₁(K)` with `v(z(Q)) = k`,
then `z([n]Q) = n z(Q) u` with `v(u - 1) ≥ 1`, and `v(z([n]Q)) = k + c`. -/
theorem zCoord_zsmul_eq_mul_unit_of_val {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ W1 v A)
    {k : ℤ} (hk : v (Mult.zCoord Q) = k) {n c : ℤ} (hn : v (n : K) = c) (hc : c + 1 ≤ 4 * k) :
    v (Mult.zCoord (n • Q)) = (k + c : ℤ) ∧
      ∃ u : K, Mult.zCoord (n • Q) = n * Mult.zCoord Q * u ∧ Vge v 1 (u - 1) := by
  have hD : v ((n : K) * Mult.zCoord Q) = (c + k : ℤ) := val_mul_coe hn hk
  have hD0 : (n : K) * Mult.zCoord Q ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hD; exact WithTop.top_ne_coe hD
  have h5 := (val_zCoord_zsmul_sub hA hQ hk n).1
  have hε : Vge v 1 ((Mult.zCoord (n • Q) - n * Mult.zCoord Q) / (n * Mult.zCoord Q)) :=
    (h5.div_val' hD).mono (by omega)
  have hu : Mult.zCoord (n • Q) =
      n * Mult.zCoord Q * (1 + (Mult.zCoord (n • Q) - n * Mult.zCoord Q) / (n * Mult.zCoord Q)) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hD0]; ring
  refine ⟨?_, _, hu, by rw [add_sub_cancel_left]; exact hε⟩
  rw [hu, val_mul_coe hD (val_one_add hε)]
  congr 1; ring

omit [DecidableEq K] in
theorem val_zCoord_of_mem_W1 {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ W1 v A) (hQ0 : Q ≠ 0) :
    ∃ k : ℤ, 1 ≤ k ∧ v (Mult.zCoord Q) = k := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ0
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA h hQ
  exact ⟨N, hN, hz⟩

/-- **Item 4.** If `v(p) = 1` and `v(m) = 0` for `p ∤ m` (residue characteristic `p`), then for
an affine `Q ∈ W₁(K)` with `v(z(Q)) = k` and `m ≠ 0`: `[m]Q` is affine,
`v(z([m]Q)) = k + v_p(m)`, and `z([m]Q) = m z(Q) u` with `v(u - 1) ≥ 1`. -/
theorem zCoord_zsmul_eq_mul_unit {p : ℕ} [Fact p.Prime] (hp1 : v (p : K) = 1)
    (hres : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → v (m : K) = 0) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ W1 v A) {k : ℤ} (hk : v (Mult.zCoord Q) = k) {m : ℤ} (hm : m ≠ 0) :
    m • Q ≠ 0 ∧ v (Mult.zCoord (m • Q)) = (k + padicValInt p m : ℤ) ∧
      ∃ u : K, Mult.zCoord (m • Q) = m * Mult.zCoord Q * u ∧ Vge v 1 (u - 1) := by
  suffices H : v (Mult.zCoord (m • Q)) = (k + padicValInt p m : ℤ) ∧
      ∃ u : K, Mult.zCoord (m • Q) = m * Mult.zCoord Q * u ∧ Vge v 1 (u - 1) from
    ⟨ne_zero_of_val_zCoord H.1, H⟩
  induction h : m.natAbs using Nat.strong_induction_on generalizing m k Q with
  | _ N ih =>
    have hk1 : 1 ≤ k := by
      have := one_le_val_zCoord hA hQ; rw [hk] at this; exact_mod_cast this
    by_cases hpm : (p : ℤ) ∣ m
    · obtain ⟨m₁, rfl⟩ := hpm
      have hm₁ : m₁ ≠ 0 := by rintro rfl; simp at hm
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have hlt : m₁.natAbs < N := by
        rw [← h, Int.natAbs_mul]
        have := (Fact.out : p.Prime).one_lt
        have : 0 < m₁.natAbs := Int.natAbs_pos.mpr hm₁
        simp only [Int.natAbs_natCast]; nlinarith
      obtain ⟨hv₀, u₀, hu₀, hu₀1⟩ := zCoord_zsmul_eq_mul_unit_of_val hA hQ hk (n := p) (c := 1)
        (by rw [Int.cast_natCast, hp1]; rfl) (by omega)
      have hpQ : (p : ℤ) • Q ∈ W1 v A := ((formalNbhd A hA).zsmul_mem
        ((mem_formalNbhd_iff hA Q).mpr hQ) _).1
      obtain ⟨hv₁, u₁, hu₁, hu₁1⟩ := ih _ hlt hpQ hv₀ hm₁ rfl
      rw [show (p : ℤ) * m₁ = m₁ * p from mul_comm _ _, mul_smul, padicValInt.mul hm₁ hp0,
        padicValInt_self]
      refine ⟨by rw [hv₁]; congr 1; push_cast; ring, u₀ * u₁, ?_, ?_⟩
      · rw [hu₁, hu₀]; push_cast; ring
      · have hu₁0 : Vge v 0 u₁ := by
          have := (hu₁1.mono (show (0 : ℤ) ≤ 1 by omega)).add
            (show Vge v 0 (1 : K) by simpa using Mult.vge_natCast (v := v) 1)
          rwa [sub_add_cancel] at this
        have := ((hu₀1.mul hu₁0).mono (show (1 : ℤ) ≤ 1 + 0 by omega)).add hu₁1
        convert this using 1
        ring
    · obtain ⟨hv, u, hu, hu1⟩ := zCoord_zsmul_eq_mul_unit_of_val hA hQ hk (n := m) (c := 0)
        (hres m hpm) (by omega)
      rw [padicValInt.eq_zero_of_not_dvd hpm]
      exact ⟨by rw [hv]; simp, u, hu, hu1⟩

/-- A consequence of item 4: for an affine `Q ∈ W₁(K)` and integers `a ≠ 0`, `b`,
`z([b]Q)/z([a]Q) = (b/a) w` with `v(w) = 0` and `v(w - 1) ≥ 1`. -/
theorem zCoord_zsmul_ratio {p : ℕ} [Fact p.Prime] (hp1 : v (p : K) = 1)
    (hres : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → v (m : K) = 0) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ W1 v A) (hQ0 : Q ≠ 0) {a b : ℤ} (ha : a ≠ 0) :
    ∃ w : K, Mult.zCoord (b • Q) / Mult.zCoord (a • Q) = (b / a : K) * w ∧ v w = 0 ∧
      Vge v 1 (w - 1) := by
  obtain ⟨k, -, hk⟩ := val_zCoord_of_mem_W1 hA hQ hQ0
  have hz0 : Mult.zCoord Q ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hk; exact WithTop.top_ne_coe hk
  obtain ⟨-, -, ua, hua, hua1⟩ := zCoord_zsmul_eq_mul_unit hA hp1 hres hQ hk ha
  have hua0 : v ua = 0 := by
    have := val_one_add hua1; rwa [add_sub_cancel] at this
  have hua0' : ua ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hua0; exact WithTop.top_ne_coe hua0
  have haK : (a : K) ≠ 0 := by
    intro h0
    have h1 := val_intCast_eq (v := v) (e := 1) hp1 hres ha
    rw [h0, v.map_zero] at h1; exact WithTop.top_ne_coe h1
  by_cases hb : b = 0
  · refine ⟨1, ?_, by rw [v.map_one], by rw [sub_self]; exact Vge.zero _⟩
    rw [hb, zero_smul, zCoord_zero, zero_div, Int.cast_zero, zero_div, zero_mul]
  obtain ⟨-, -, ub, hub, hub1⟩ := zCoord_zsmul_eq_mul_unit hA hp1 hres hQ hk hb
  refine ⟨ub / ua, ?_, ?_, ?_⟩
  · rw [hua, hub]; field_simp
  · rw [v.map_div, hua0]
    have := val_one_add hub1; rw [add_sub_cancel] at this; rw [this]; rfl
  · have : ub / ua - 1 = ((ub - 1) - (ua - 1)) / ua := by field_simp; ring
    rw [this]; exact (hub1.sub hua1).div_unit hua0

end General

/-! ### The subgroups `E_k(π)` of `E(K₀)` -/

section K0

/-- `E` is `y² = x³ + A x` with `A = -d²`, integral at every prime of `ℤ[s]`. -/
theorem vP_genA_nonneg (π : Zs) (hπ : Prime π) : 0 ≤ vP π hπ (-genD ^ 2) := by
  rw [show -genD ^ 2 = Zs.toK0 (-genDZ ^ 2) by simp]
  exact vP_toK0_nonneg _ _

/-- `E_k(π)`: the subgroup `W_k(K₀)` of `E(K₀)` at the valuation `v_π` of a prime `π` of
`ℤ[s]`, the points `P ∈ E₁(π)` (`P = O` or `v_π(x(P)) < 0`) with `v_π(z(P)) ≥ k`. -/
noncomputable def Ek (π : Zs) (hπ : Prime π) (k : ℤ) : AddSubgroup genCurve.toAffine.Point :=
  formalFilt (-genD ^ 2) (vP_genA_nonneg π hπ) k

theorem mem_Ek_iff {π : Zs} (hπ : Prime π) (k : ℤ) (P : genCurve.toAffine.Point) :
    P ∈ Ek π hπ k ↔ P ∈ W1 (vP π hπ) (-genD ^ 2) ∧
      (k : WithTop ℤ) ≤ vP π hπ (Mult.zCoord (A := -genD ^ 2) P) := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {π : Zs}

/-- `v_π(p) = 1` at a prime `π` above an odd prime `p`. -/
theorem vP_natCast_self (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    vP π hπ (p : K0) = 1 := by
  rw [vP_apply hπ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    Mult.vp_natCast_self hp2 hπ hπp]; rfl

/-- The residue characteristic at a prime `π` above `p` is `p`. -/
theorem vP_intCast_of_not_dvd (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) (m : ℤ)
    (hm : ¬ (p : ℤ) ∣ m) : vP π hπ (m : K0) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  rw [vP_apply hπ (Int.cast_ne_zero.mpr hm0), Mult.vp_intCast hp2 hπ hπp hm0,
    padicValInt.eq_zero_of_not_dvd hm]; rfl

/-- `v_s(2) = 2`. -/
theorem vS_two_eq : vS ((2 : ℕ) : K0) = 2 := by
  rw [vP_apply _ (by norm_num), Nat.cast_ofNat, vS_two]; rfl

/-- The residue characteristic at `(s)` is `2`. -/
theorem vS_intCast_of_not_dvd (m : ℤ) (hm : ¬ ((2 : ℕ) : ℤ) ∣ m) : vS (m : K0) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  rw [vP_apply _ (Int.cast_ne_zero.mpr hm0), vS_int hm0,
    padicValInt.eq_zero_of_not_dvd hm]; rfl

/-- **Item 4 on `K₀`.** At a prime `π` above an odd prime `p`, for an affine `Q ∈ E₁(π)` with
`ν_π(Q) = k` and `m ≠ 0`: `[m]Q` is affine, `ν_π([m]Q) = k + v_p(m)`, and
`z([m]Q) = m z(Q) u` with `v_π(u - 1) ≥ 1`. -/
theorem zCoord_zsmul_eq_mul_unit_K0 (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs))
    {Q : genCurve.toAffine.Point} (hQ : Q ∈ Ek π hπ 1) {k : ℤ}
    (hk : vP π hπ (Mult.zCoord (A := -genD ^ 2) Q) = k) {m : ℤ} (hm : m ≠ 0) :
    m • Q ≠ 0 ∧ vP π hπ (Mult.zCoord (A := -genD ^ 2) (m • Q)) = (k + padicValInt p m : ℤ) ∧
      ∃ u : K0, Mult.zCoord (A := -genD ^ 2) (m • Q) = m * Mult.zCoord (A := -genD ^ 2) Q * u ∧
        Vge (vP π hπ) 1 (u - 1) :=
  zCoord_zsmul_eq_mul_unit (vP_genA_nonneg π hπ) (vP_natCast_self hp2 hπ hπp)
    (vP_intCast_of_not_dvd hp2 hπ hπp) hQ.1 hk hm

/-- The ratio form of item 4 on `K₀`, at a prime `π` above an odd prime `p`. -/
theorem zCoord_zsmul_ratio_K0 (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs))
    {Q : genCurve.toAffine.Point} (hQ : Q ∈ Ek π hπ 1) (hQ0 : Q ≠ 0) {a b : ℤ} (ha : a ≠ 0) :
    ∃ w : K0, Mult.zCoord (A := -genD ^ 2) (b • Q) / Mult.zCoord (A := -genD ^ 2) (a • Q) =
      (b / a : K0) * w ∧ vP π hπ w = 0 ∧ Vge (vP π hπ) 1 (w - 1) :=
  zCoord_zsmul_ratio (vP_genA_nonneg π hπ) (vP_natCast_self hp2 hπ hπp)
    (vP_intCast_of_not_dvd hp2 hπ hπp) hQ.1 hQ0 ha

/-- **Item 3 on `K₀` at `(s)`.** `[n]E_k(s) ⊆ E_{k + v_s(n)}(s)` with `v_s(n) = 2 v₂(n)`. -/
theorem zsmul_mem_Ek_sqrt2 {n : ℤ} (hn : n ≠ 0) {k : ℤ} (hk : 1 ≤ k)
    {Q : genCurve.toAffine.Point} (hQ : Q ∈ Ek sqrt2Z prime_sqrt2Z k) :
    n • Q ∈ Ek sqrt2Z prime_sqrt2Z (k + 2 * padicValInt 2 n) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  zsmul_mem_formalFilt_add_val (p := 2) (vP_genA_nonneg _ _) vS_two_eq (by norm_num) hn hk hQ

/-- **Item 3 on `K₀` above an odd prime.** `[n]E_k(π) ⊆ E_{k + v_p(n)}(π)`. -/
theorem zsmul_mem_Ek_of_dvd (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {n : ℤ}
    (hn : n ≠ 0) {k : ℤ} (hk : 1 ≤ k) {Q : genCurve.toAffine.Point} (hQ : Q ∈ Ek π hπ k) :
    n • Q ∈ Ek π hπ (k + padicValInt p n) := by
  have := zsmul_mem_formalFilt_add_val (vP_genA_nonneg π hπ) (vP_natCast_self hp2 hπ hπp)
    (by norm_num) hn hk hQ
  rwa [one_mul] at this

end K0

end ZInQ.Assembly
