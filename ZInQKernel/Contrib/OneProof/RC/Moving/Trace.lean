import ZInQKernel.Contrib.OneProof.RC.Moving.SL2

/-!
# Lane RC4 (moving character): the trace lemma (4.4d) and the trace bound `c_E = 16d + 21`

Manuscript (11/5 version), Proposition `ex:arith-moving-character`, proof, tex lines 3635–3692.

Everything in this file is `PROVED`:

* `trace_lemma` — **(4.4d)** (tex 3635–3660): for `δ = 2^ν`, `ν ≥ 3`, and any `A ∈ SL₂(ℤ₂)`,
  one of `A, A U(δ), A D(1+δ), A D(1+2δ)` has both trace distances to `2` and `−2` of
  2-adic valuation at most `2ν + 1`; the proof is Elliot's case analysis (equal-parity diagonal;
  both even: `c` odd and `U(δ)` changes the trace by `cδ`; both odd: the two diagonal changes
  `δ((a−f)+aδ)/(1+δ)` and `2δ((a−f)+2aδ)/(1+2δ)`; every chosen change has valuation `≥ 3`);
* `lift_trace_bound` — (tex 3662–3668): if `Γ_ν ⊂ ρ(N)` then every `σ₀` has a right multiple
  `σ = σ₀ n`, `n ∈ N`, with that trace bound (the multipliers of (4.4d) lie in `Γ_ν`);
* `tate_trace_control` — (4.4c) + (4.4d): with Serre's `Γ_d ⊂ J`, every `σ₀ ∈ G_{F_∞}` has
  `σ ∈ σ₀ G_{L_∞}` with `v₂(2 ± tr ρ_T(σ)) ≤ c_E`, `c_E = 2ν + 1 = 16d + 21` (tex 3627, 3635);
* `frobenius_bounds` — (tex 3686–3693): from `a_r ≡ tr ρ_T(σ) (mod 2^{B'})`, `r ≡ 1 (mod 2^{B'})`
  and `B' > c_E`: `v₂(2 ± a_r) ≤ c_E` and `v₂(1 ± a_r + r) ≤ c_E`; with `det_one_add`,
  `det_one_sub` (`det(1 ± F) = 1 ± tr F + det F`) this is `v₂ det(1 ± Fr_r) ≤ c_E`; and
  `a_r − 2χ_h(r)` for `χ_h(r) = ±1`.

`v₂(x) ≤ k` is written `v2Le x k := ¬ 2^{k+1} ∣ x` (so `v₂(0) = ∞`).
-/

open Matrix
open scoped MatrixGroups commutatorElement

namespace ZInQ.Manuscript.RC.Moving

noncomputable section

/-- `v₂(x) ≤ k` in `ℤ₂`: `x ∉ 2^{k+1} ℤ₂`. -/
def v2Le (x : ℤ_[2]) (k : ℕ) : Prop := ¬ (2 : ℤ_[2]) ^ (k + 1) ∣ x

/-- The trace of `A ∈ SL₂(ℤ₂)`. -/
def tr (A : SL(2, ℤ_[2])) : ℤ_[2] := Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ_[2])

/-- `tr A = a + f` (helper). -/
theorem tr_eq (A : SL(2, ℤ_[2])) : tr A = A 0 0 + A 1 1 := by
  rw [tr, Matrix.trace_fin_two]

/-- `tr(A·1) = tr A` (helper). -/
theorem tr_mul_one (A : SL(2, ℤ_[2])) : tr (A * 1) = tr A := by rw [mul_one]

/-- `tr(A U(x)) = tr A + c x` (tex 3648–3649). -/
theorem tr_mul_U (A : SL(2, ℤ_[2])) (x : ℤ_[2]) : tr (A * U x) = tr A + A 1 0 * x := by
  simp only [tr, Matrix.trace_fin_two, Matrix.SpecialLinearGroup.coe_mul, U_coe,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- `(tr(A D(v)) − tr A) · v = (v − 1)(a v − f)` (tex 3650–3654); for `v = 1 + δ` this is
Elliot's change `δ((a−f)+aδ)/(1+δ)`. -/
theorem tr_mul_D (A : SL(2, ℤ_[2])) (v : ℤ_[2]ˣ) :
    (tr (A * D v) - tr A) * (v : ℤ_[2]) = ((v : ℤ_[2]) - 1) * (A 0 0 * v - A 1 1) := by
  have h1 : ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (v : ℤ_[2]) = 1 := Units.inv_mul v
  simp only [tr, Matrix.trace_fin_two, Matrix.SpecialLinearGroup.coe_mul, D_coe,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (A 1 1) * h1

/-! ### Parity in `ℤ₂` -/

theorem two_dvd_iff_toZMod (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  norm_num

/-- A nonzero element of `𝐅₂` is `1` (helper). -/
theorem zmod_two_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- Two odd elements of `ℤ₂` have even sum. -/
theorem two_dvd_add_of_odd {a f : ℤ_[2]} (ha : ¬ (2 : ℤ_[2]) ∣ a) (hf : ¬ (2 : ℤ_[2]) ∣ f) :
    (2 : ℤ_[2]) ∣ a + f := by
  rw [two_dvd_iff_toZMod] at ha hf ⊢
  rw [map_add, zmod_two_eq_one ha, zmod_two_eq_one hf]
  decide

/-- Cancelling a power of `2` (helper). -/
theorem two_pow_add_dvd_iff (j i : ℕ) (X : ℤ_[2]) :
    (2 : ℤ_[2]) ^ (j + i) ∣ 2 ^ j * X ↔ (2 : ℤ_[2]) ^ i ∣ X := by
  rw [pow_add]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero')

/-- `8 ∤ 4` in `ℤ₂` (helper; the two forbidden values `±2` differ by `4`). -/
theorem not_eight_dvd_four : ¬ (8 : ℤ_[2]) ∣ 4 := by
  intro h
  have h' : (4 : ℤ_[2]) * 2 ∣ 4 * 1 := by norm_num; exact h
  rw [mul_dvd_mul_iff_left (by norm_num : (4 : ℤ_[2]) ≠ 0)] at h'
  exact not_two_dvd_one h'

/-- `8 ∣ 2^ν` for `ν ≥ 3` (helper; "all the chosen changes have valuation at least three"). -/
theorem eight_dvd_two_pow {ν : ℕ} (hν : 3 ≤ ν) : (8 : ℤ_[2]) ∣ 2 ^ ν := by
  have : (8 : ℤ_[2]) = 2 ^ 3 := by norm_num
  rw [this]
  exact pow_dvd_pow 2 hν

/-! ### The trace lemma (4.4d) -/

/-- Elliot's reduction (tex 3644–3646, 3658–3660): if `tr A` is within `2^{2ν+2}` of `e = ±2` and
the change `Δ = tr(AM) − tr A` has valuation `≥ 3` and `≤ 2ν + 1`, then `AM` has both trace
distances of valuation `≤ 2ν + 1`. -/
theorem bounds_of_change (ν : ℕ) (hν : 3 ≤ ν) (t t' e : ℤ_[2]) (he : e = 2 ∨ e = -2)
    (hnear : (2 : ℤ_[2]) ^ (2 * ν + 2) ∣ t - e) (h8 : (8 : ℤ_[2]) ∣ t' - t)
    (hΔ : ¬ (2 : ℤ_[2]) ^ (2 * ν + 2) ∣ t' - t) :
    v2Le (t' - 2) (2 * ν + 1) ∧ v2Le (t' + 2) (2 * ν + 1) := by
  have hnearer : v2Le (t' - e) (2 * ν + 1) := by
    intro h
    apply hΔ
    have := dvd_sub h hnear
    convert this using 1
    ring
  have h8near : (8 : ℤ_[2]) ∣ t - e := by
    refine (?_ : (8 : ℤ_[2]) ∣ 2 ^ (2 * ν + 2)).trans hnear
    have : (8 : ℤ_[2]) = 2 ^ 3 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 (by omega)
  have hfar : v2Le (t' + e) (2 * ν + 1) := by
    intro h
    have h8' : (8 : ℤ_[2]) ∣ t' + e :=
      (by
        have : (8 : ℤ_[2]) = 2 ^ 3 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega) : (8 : ℤ_[2]) ∣ 2 ^ (2 * ν + 1 + 1)).trans h
    have h4 : (8 : ℤ_[2]) ∣ 2 * e := by
      have := dvd_sub (dvd_sub h8' h8) h8near
      convert this using 1
      ring
    rcases he with rfl | rfl
    · exact not_eight_dvd_four (by norm_num at h4 ⊢; exact h4)
    · exact not_eight_dvd_four (by
        have := dvd_neg.2 h4
        norm_num at this ⊢
        exact this)
  rcases he with rfl | rfl
  · exact ⟨hnearer, hfar⟩
  · refine ⟨?_, ?_⟩
    · simpa [sub_eq_add_neg] using hfar
    · simpa [sub_neg_eq_add] using hnearer

/-- **The trace lemma (4.4d)** (tex 3635–3660, PROVED).  Put `δ = 2^ν` with `ν ≥ 3`.  For every
`A ∈ SL₂(ℤ₂)` one of `A, A U(δ), A D(1+δ), A D(1+2δ)` has both trace distances to `2` and `−2`
of valuation at most `2ν + 1`. -/
theorem trace_lemma (ν : ℕ) (hν : 3 ≤ ν) (A : SL(2, ℤ_[2])) :
    ∃ M : SL(2, ℤ_[2]),
      (M = 1 ∨ M = U ((2 : ℤ_[2]) ^ ν) ∨ M = D (onePlusTwoPow ν (by omega)) ∨
        M = D (onePlusTwoPow (ν + 1) (by omega))) ∧
      v2Le (tr (A * M) - 2) (2 * ν + 1) ∧ v2Le (tr (A * M) + 2) (2 * ν + 1) := by
  by_cases h0 : v2Le (tr A - 2) (2 * ν + 1) ∧ v2Le (tr A + 2) (2 * ν + 1)
  · exact ⟨1, Or.inl rfl, by simpa using h0⟩
  -- `A` itself fails: its trace is within `2^{2ν+2}` of `e = ±2` (tex 3645–3646)
  obtain ⟨e, he, hnear⟩ : ∃ e : ℤ_[2], (e = 2 ∨ e = -2) ∧ (2 : ℤ_[2]) ^ (2 * ν + 2) ∣ tr A - e := by
    rw [not_and_or] at h0
    rcases h0 with h | h
    · refine ⟨2, Or.inl rfl, ?_⟩
      have := not_not.1 h
      rwa [show 2 * ν + 1 + 1 = 2 * ν + 2 by ring] at this
    · refine ⟨-2, Or.inr rfl, ?_⟩
      have := not_not.1 h
      rw [show 2 * ν + 1 + 1 = 2 * ν + 2 by ring] at this
      rwa [sub_neg_eq_add]
  suffices key : ∃ M : SL(2, ℤ_[2]),
      (M = 1 ∨ M = U ((2 : ℤ_[2]) ^ ν) ∨ M = D (onePlusTwoPow ν (by omega)) ∨
        M = D (onePlusTwoPow (ν + 1) (by omega))) ∧
      (8 : ℤ_[2]) ∣ tr (A * M) - tr A ∧ ¬ (2 : ℤ_[2]) ^ (2 * ν + 2) ∣ tr (A * M) - tr A by
    obtain ⟨M, hM, h8, hΔ⟩ := key
    exact ⟨M, hM, bounds_of_change ν hν (tr A) (tr (A * M)) e he hnear h8 hΔ⟩
  set a := A 0 0 with ha_def
  set b := A 0 1 with hb_def
  set c := A 1 0 with hc_def
  set f := A 1 1 with hf_def
  have hdet : a * f - b * c = 1 := by
    have := A.det_coe
    rwa [Matrix.det_fin_two] at this
  have htr : tr A = a + f := tr_eq A
  set δ : ℤ_[2] := 2 ^ ν with hδ_def
  have h8δ : (8 : ℤ_[2]) ∣ δ := eight_dvd_two_pow hν
  -- the diagonal entries have the same parity (tex 3647)
  have hpar : (2 : ℤ_[2]) ∣ a + f := by
    have h2e : (2 : ℤ_[2]) ∣ e := by rcases he with rfl | rfl <;> simp
    have h2near : (2 : ℤ_[2]) ∣ tr A - e :=
      (dvd_pow_self 2 (by omega : 2 * ν + 2 ≠ 0)).trans hnear
    have := dvd_add h2near h2e
    rw [sub_add_cancel, htr] at this
    exact this
  by_cases hae : (2 : ℤ_[2]) ∣ a
  · -- both even: `c` is odd, and `A U(δ)` changes the trace by `cδ` (tex 3647–3649)
    have hfe : (2 : ℤ_[2]) ∣ f := by
      have := dvd_sub hpar hae
      rwa [add_sub_cancel_left] at this
    have hco : ¬ (2 : ℤ_[2]) ∣ c := by
      intro hc
      apply not_two_dvd_one
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left hae _) (dvd_mul_of_dvd_right hc _)
    refine ⟨U δ, Or.inr (Or.inl rfl), ?_, ?_⟩
    · rw [tr_mul_U, add_sub_cancel_left]
      exact dvd_mul_of_dvd_right h8δ _
    · rw [tr_mul_U, add_sub_cancel_left]
      intro h
      apply hco
      have hcδ : c * δ = 2 ^ ν * c := by rw [hδ_def]; ring
      have h' : (2 : ℤ_[2]) ^ (ν + 1) ∣ 2 ^ ν * c := by
        rw [← hcδ]
        exact (pow_dvd_pow 2 (by omega : ν + 1 ≤ 2 * ν + 2)).trans h
      rw [two_pow_add_dvd_iff, pow_one] at h'
      exact h'
  · -- both odd (tex 3650–3657)
    have hfo : ¬ (2 : ℤ_[2]) ∣ f := by
      intro hf
      apply hae
      have := dvd_sub hpar hf
      rwa [add_sub_cancel_right] at this
    set v₁ := onePlusTwoPow ν (by omega) with hv₁_def
    have hv₁ : (v₁ : ℤ_[2]) = 1 + δ := onePlusTwoPow_coe ν _
    set v₂ := onePlusTwoPow (ν + 1) (by omega) with hv₂_def
    have hv₂ : (v₂ : ℤ_[2]) = 1 + 2 * δ := by
      rw [hv₂_def, onePlusTwoPow_coe, pow_succ, mul_comm]
    -- the first diagonal change, times the unit `1 + δ`
    have hΔ₁ : (tr (A * D v₁) - tr A) * (v₁ : ℤ_[2]) = δ * ((a - f) + a * δ) := by
      rw [tr_mul_D, hv₁]; ring
    have hΔ₂ : (tr (A * D v₂) - tr A) * (v₂ : ℤ_[2]) = 2 * δ * ((a - f) + 2 * a * δ) := by
      rw [tr_mul_D, hv₂]; ring
    have h8Δ₁ : (8 : ℤ_[2]) ∣ tr (A * D v₁) - tr A := by
      rw [← Units.dvd_mul_right (u := v₁), hΔ₁]
      exact dvd_mul_of_dvd_left h8δ _
    have h8Δ₂ : (8 : ℤ_[2]) ∣ tr (A * D v₂) - tr A := by
      rw [← Units.dvd_mul_right (u := v₂), hΔ₂]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h8δ _) _
    by_cases hz : (2 : ℤ_[2]) ^ ν ∣ a - f
    · obtain ⟨z, hz⟩ := hz
      by_cases hze : (2 : ℤ_[2]) ∣ z
      · -- `a − f = δz`, `z` even: the first change has valuation `2ν` (tex 3656–3657)
        refine ⟨D v₁, Or.inr (Or.inr (Or.inl rfl)), h8Δ₁, ?_⟩
        rw [← Units.dvd_mul_right (u := v₁), hΔ₁, hz]
        intro h
        have e1 : δ * (2 ^ ν * z + a * δ) = 2 ^ (2 * ν) * (z + a) := by rw [hδ_def]; ring
        rw [e1] at h
        have h' : (2 : ℤ_[2]) ^ (2 * ν + 2) ∣ 2 ^ (2 * ν) * (z + a) := h
        rw [two_pow_add_dvd_iff] at h'
        apply hae
        have h2 : (2 : ℤ_[2]) ∣ z + a := (dvd_pow_self 2 (by norm_num)).trans h'
        have := dvd_sub h2 hze
        rwa [add_sub_cancel_left] at this
      · -- `z` odd: the second change has valuation `2ν + 1` (tex 3657)
        refine ⟨D v₂, Or.inr (Or.inr (Or.inr rfl)), h8Δ₂, ?_⟩
        rw [← Units.dvd_mul_right (u := v₂), hΔ₂, hz]
        intro h
        have e1 : 2 * δ * (2 ^ ν * z + 2 * a * δ) = 2 ^ (2 * ν + 1) * (z + 2 * a) := by
          rw [hδ_def]; ring
        rw [e1] at h
        have h' : (2 : ℤ_[2]) ^ (2 * ν + 1 + 1) ∣ 2 ^ (2 * ν + 1) * (z + 2 * a) := by
          rwa [show 2 * ν + 1 + 1 = 2 * ν + 2 by ring]
        rw [two_pow_add_dvd_iff, pow_one] at h'
        apply hze
        have := dvd_sub h' (dvd_mul_right 2 a)
        rwa [add_sub_cancel_right] at this
    · -- `v₂(a − f) < ν`: the first change has valuation at most `2ν − 1` (tex 3655)
      refine ⟨D v₁, Or.inr (Or.inr (Or.inl rfl)), h8Δ₁, ?_⟩
      rw [← Units.dvd_mul_right (u := v₁), hΔ₁]
      intro h
      apply hz
      have h' : (2 : ℤ_[2]) ^ (ν + (ν + 2)) ∣ 2 ^ ν * ((a - f) + a * δ) := by
        rw [show ν + (ν + 2) = 2 * ν + 2 by ring]
        exact h
      rw [two_pow_add_dvd_iff] at h'
      have h'' : (2 : ℤ_[2]) ^ ν ∣ (a - f) + a * δ :=
        (pow_dvd_pow 2 (by omega : ν ≤ ν + 2)).trans h'
      have := dvd_sub h'' (dvd_mul_left δ a)
      rwa [add_sub_cancel_right] at this

/-- The four multipliers of (4.4d) lie in `Γ_ν` (tex 3663–3664). -/
theorem multiplier_mem_Γ (ν : ℕ) (hν : 3 ≤ ν) (M : SL(2, ℤ_[2]))
    (hM : M = 1 ∨ M = U ((2 : ℤ_[2]) ^ ν) ∨ M = D (onePlusTwoPow ν (by omega)) ∨
      M = D (onePlusTwoPow (ν + 1) (by omega))) : M ∈ Γ ν := by
  rcases hM with rfl | rfl | rfl | rfl
  · exact (Γ ν).one_mem
  · exact U_mem_Γ dvd_rfl
  · exact D_mem_Γ (by rw [onePlusTwoPow_coe, add_sub_cancel_left])
  · exact D_mem_Γ (by
      rw [onePlusTwoPow_coe, add_sub_cancel_left]
      exact pow_dvd_pow 2 (by omega))

/-- **Choosing the multiplier** (tex 3662–3668, PROVED): if `Γ_ν ⊂ ρ(N)` (as (4.4c) gives for
`N = G_{L_∞}`), every `σ₀` has a right multiple `σ = σ₀ n`, `n ∈ N`, with
`v₂(2 ± tr ρ(σ)) ≤ 2ν + 1`. -/
theorem lift_trace_bound {G : Type*} [Group G] (ρ : G →* SL(2, ℤ_[2])) (N : Subgroup G)
    (ν : ℕ) (hν : 3 ≤ ν) (hΓ : Γ ν ≤ N.map ρ) (σ₀ : G) :
    ∃ σ : G, σ₀⁻¹ * σ ∈ N ∧ v2Le (tr (ρ σ) - 2) (2 * ν + 1) ∧
      v2Le (tr (ρ σ) + 2) (2 * ν + 1) := by
  obtain ⟨M, hM, h1, h2⟩ := trace_lemma ν hν (ρ σ₀)
  obtain ⟨n, hn, hρn⟩ := hΓ (multiplier_mem_Γ ν hν M hM)
  refine ⟨σ₀ * n, by simpa using hn, ?_, ?_⟩
  · rw [map_mul, hρn]; exact h1
  · rw [map_mul, hρn]; exact h2

/-- Elliot's level `ν = 4m + 2 = 8d + 10` (tex 3627). -/
def νE (d : ℕ) : ℕ := 8 * d + 10

/-- Elliot's trace constant `c_E = 2ν + 1 = 16d + 21` (tex 3635); it depends only on `d`, i.e.
on the fixed Tate image, not on `K`, `n`, `B` or the active list. -/
def cE (d : ℕ) : ℕ := 16 * d + 21

theorem cE_eq (d : ℕ) : cE d = 2 * νE d + 1 := by unfold cE νE; ring

/-- **Tate-trace control** ((4.4c) + (4.4d), tex 3597–3668, PROVED from its hypotheses).
`G` plays `G_{ℚ(μ_{2^∞})}`, `ρ` the Tate representation on it, `GF` plays `G_{F_∞}`
(index at most two), `HL` plays `G_{L_∞} ⊂ G_{F_∞}` with `G_{F_∞}/G_{L_∞}` abelian.  If
`Γ_d ⊂ ρ(G)` (Serre), every `σ₀ ∈ G_{F_∞}` (the lift of the prescribed Kummer automorphism) has a
modification `σ ∈ σ₀ G_{L_∞} ⊂ G_{F_∞}` — so `σ` acts on `L_∞` as `σ₀` does — with
`v₂(2 ± tr ρ(σ)) ≤ c_E = 16d + 21`. -/
theorem tate_trace_control {G : Type*} [Group G] (ρ : G →* SL(2, ℤ_[2])) (GF HL : Subgroup G)
    (d : ℕ) (hSerre : Γ d ≤ ρ.range) (hidx : GF.index = 1 ∨ GF.index = 2)
    (hab : ⁅GF, GF⁆ ≤ HL) (hLF : HL ≤ GF) (σ₀ : G) (hσ₀ : σ₀ ∈ GF) :
    ∃ σ ∈ GF, σ₀⁻¹ * σ ∈ HL ∧ v2Le (tr (ρ σ) - 2) (cE d) ∧ v2Le (tr (ρ σ) + 2) (cE d) := by
  have h44c : Γ (νE d) ≤ HL.map ρ := four_four_c ρ GF HL d hSerre hidx hab
  obtain ⟨σ, hσL, h1, h2⟩ := lift_trace_bound ρ HL (νE d) (by unfold νE; omega) h44c σ₀
  refine ⟨σ, ?_, hσL, by rw [cE_eq]; exact h1, by rw [cE_eq]; exact h2⟩
  have := GF.mul_mem hσ₀ (hLF hσL)
  simpa using this

/-! ### From the Galois element to `a_r` (tex 3686–3693) -/

/-- Transfer of a valuation bound along a congruence modulo `2^{B'}`, `B' > c`. -/
theorem not_dvd_of_congr (x : ℤ) (t : ℤ_[2]) (B' c : ℕ) (hB : c + 1 ≤ B')
    (hcong : (2 : ℤ_[2]) ^ B' ∣ (x : ℤ_[2]) - t) (h : v2Le t c) : ¬ (2 : ℤ) ^ (c + 1) ∣ x := by
  intro hx
  apply h
  have hx' : (2 : ℤ_[2]) ^ (c + 1) ∣ (x : ℤ_[2]) := by
    have := map_dvd (Int.castRingHom ℤ_[2]) hx
    simpa using this
  have := dvd_sub hx' ((pow_dvd_pow 2 hB).trans hcong)
  simpa using this

/-- Divisibility of an integer by `2^k` is the same in `ℤ` and in `ℤ₂`. -/
theorem int_two_pow_dvd_iff (k : ℕ) (z : ℤ) :
    (2 : ℤ_[2]) ^ k ∣ (z : ℤ_[2]) ↔ (2 : ℤ) ^ k ∣ z := by
  rw [← sub_zero (z : ℤ_[2]), ← toZModPow_eq_iff, map_intCast, map_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- `det(1 + F) = 1 + tr F + det F` for `2 × 2` matrices (tex 3690). -/
theorem det_one_add {R : Type*} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) :
    (1 + F).det = 1 + F.trace + F.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

/-- `det(1 − F) = 1 − tr F + det F` for `2 × 2` matrices (tex 3690). -/
theorem det_one_sub {R : Type*} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) :
    (1 - F).det = 1 - F.trace + F.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

/-- **The bounds at `r`** (tex 3686–3693, PROVED): if `a_r ≡ t (mod 2^{B'})` with
`t = tr ρ_T(σ)`, `r ≡ 1 (mod 2^{B'})`, `B' > c` and `v₂(2 ± t) ≤ c`, then `v₂(2 ± a_r) ≤ c`,
`v₂(1 ± a_r + r) ≤ c` (`= v₂ det(1 ± Fr_r)` since `tr Fr_r = a_r`, `det Fr_r = r`), and
`v₂(a_r − 2χ) ≤ c` for `χ = ±1` (the constituents `χ_h` unramified at `r`). -/
theorem frobenius_bounds (ar r : ℤ) (t : ℤ_[2]) (c B' : ℕ) (hB : c + 1 ≤ B')
    (htr : (2 : ℤ_[2]) ^ B' ∣ (ar : ℤ_[2]) - t) (hr : (2 : ℤ) ^ B' ∣ r - 1)
    (h1 : v2Le (t - 2) c) (h2 : v2Le (t + 2) c) :
    ¬ (2 : ℤ) ^ (c + 1) ∣ 2 + ar ∧ ¬ (2 : ℤ) ^ (c + 1) ∣ 2 - ar ∧
      ¬ (2 : ℤ) ^ (c + 1) ∣ 1 + ar + r ∧ ¬ (2 : ℤ) ^ (c + 1) ∣ 1 - ar + r ∧
      (∀ χ : ℤ, (χ = 1 ∨ χ = -1) → ¬ (2 : ℤ) ^ (c + 1) ∣ ar - 2 * χ) := by
  have hr' : (2 : ℤ_[2]) ^ B' ∣ (r : ℤ_[2]) - 1 := by
    have := map_dvd (Int.castRingHom ℤ_[2]) hr
    simpa using this
  have h2' : v2Le (2 + t) c := by rwa [add_comm]
  have h1' : v2Le (2 - t) c := by
    unfold v2Le at h1 ⊢
    rwa [← neg_sub, dvd_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine not_dvd_of_congr _ (2 + t) B' c hB ?_ h2'
    convert htr using 1; push_cast; ring
  · refine not_dvd_of_congr _ (2 - t) B' c hB ?_ h1'
    have := dvd_neg.2 htr
    convert this using 1; push_cast; ring
  · refine not_dvd_of_congr _ (2 + t) B' c hB ?_ h2'
    have := dvd_add htr hr'
    convert this using 1; push_cast; ring
  · refine not_dvd_of_congr _ (2 - t) B' c hB ?_ h1'
    have := dvd_sub hr' htr
    convert this using 1; push_cast; ring
  · intro χ hχ
    rcases hχ with rfl | rfl
    · refine not_dvd_of_congr _ (t - 2) B' c hB ?_ h1
      convert htr using 1; push_cast; ring
    · refine not_dvd_of_congr _ (t + 2) B' c hB ?_ h2
      convert htr using 1; push_cast; ring

end

end ZInQ.Manuscript.RC.Moving
