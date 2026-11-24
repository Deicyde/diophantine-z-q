import ZInQKernel.Contrib.PoleRC.Defs

/-!
# The squareclass bookkeeping (`diophantine_zq.tex` lines 1020–1032)

From `B` as in Theorem 5.2: a positive signed divisor `m` of `2730` (as the six bits `bᵢ`),
and positive squarefree `β, θ` with `A = mB = β s²`, `H = A(A − B²) = θ c²`, `β ≡ 17`,
`θ ≡ 1 (mod 24)`, coprime, each a square modulo every prime of the other.

Writing `B = N/D²` (`D² = den B`), `N = k² r` with `r` squarefree, `r = r₀ r₁` with
`r₀ = gcd(r, 2730)`: `m = r₀ f / gcd(r₀, f)²` for the divisor `f` of `5·7·13` with
`f r₁ ≡ 17 (mod 24)`, `β = f r₁`, and `θ` is the squarefree part of `T = D² − N/m`, so that
`H = T (mB/D)²`.
-/

namespace ZInQ.Manuscript.PoleRC

/-- The eight products of subsets of `{5, 7, 13}`; they represent `(ℤ/24)ˣ`. -/
def fSet : Finset ℕ := {1, 5, 7, 13, 35, 65, 91, 455}

theorem exists_f (x : ℕ) (h2 : ¬ 2 ∣ x) (h3 : ¬ 3 ∣ x) : ∃ f ∈ fSet, f * x % 24 = 17 := by
  have : x % 24 = 1 ∨ x % 24 = 5 ∨ x % 24 = 7 ∨ x % 24 = 11 ∨ x % 24 = 13 ∨ x % 24 = 17 ∨
      x % 24 = 19 ∨ x % 24 = 23 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact ⟨65, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨13, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨455, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨91, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨5, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨1, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨35, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨7, by decide, by rw [Nat.mul_mod, h]⟩

set_option maxRecDepth 100000 in
theorem divisors_2730 : Nat.divisors 2730 = {1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39,
    42, 65, 70, 78, 91, 105, 130, 182, 195, 210, 273, 390, 455, 546, 910, 1365, 2730} := by
  decide

set_option maxRecDepth 100000 in
theorem fSet_dvd : ∀ f ∈ fSet, f ∣ 2730 := by decide

set_option maxRecDepth 100000 in
theorem m_of_r0f : ∀ r₀ ∈ Nat.divisors 2730, ∀ f ∈ fSet,
    r₀ * f / Nat.gcd r₀ f ^ 2 * Nat.gcd r₀ f ^ 2 = r₀ * f ∧ r₀ * f / Nat.gcd r₀ f ^ 2 ∣ 2730 := by
  rw [divisors_2730]; decide

set_option maxRecDepth 100000 in
theorem m_bits : ∀ m ∈ Nat.divisors 2730,
    m = (if 2 ∣ m then 2 else 1) * (if 3 ∣ m then 3 else 1) * (if 5 ∣ m then 5 else 1) *
      (if 7 ∣ m then 7 else 1) * (if 13 ∣ m then 13 else 1) := by
  rw [divisors_2730]; decide

theorem sq_mod_24 {x : ℕ} (h2 : ¬ 2 ∣ x) (h3 : ¬ 3 ∣ x) : x * x % 24 = 1 := by
  have : x % 24 = 1 ∨ x % 24 = 5 ∨ x % 24 = 7 ∨ x % 24 = 11 ∨ x % 24 = 13 ∨ x % 24 = 17 ∨
      x % 24 = 19 ∨ x % 24 = 23 := by omega
  rw [Nat.mul_mod]
  rcases this with h | h | h | h | h | h | h | h <;> rw [h]

theorem squarefree_2730 : Squarefree (2730 : ℕ) := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
  simp [Nat.primeFactorsList]
  norm_num

/-- `p⁴ ∣ num B` when `v_p(B) ≥ 4`. -/
theorem pow4_dvd_num {B : ℚ} {p : ℕ} (hp : p.Prime) (h : 4 ≤ padicValRat p B) (hB : B ≠ 0) :
    p ^ 4 ∣ B.num.natAbs := by
  rw [padicValRat_def] at h
  have h' : 4 ≤ padicValNat p B.num.natAbs := by
    have : (0 : ℤ) ≤ padicValNat p B.den := Nat.cast_nonneg _
    have : (4 : ℤ) ≤ padicValInt p B.num := by linarith
    exact_mod_cast this
  exact (padicValNat_dvd_iff_le_of_ne_one hp.ne_one
    (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hB))).mpr h'

/-- **The squareclass bookkeeping** (lines 1020–1032). -/
theorem bookkeeping (B : ℚ) (hden : IsSquare B.den) (hpos : 0 < B) (hlt : B < 1 / 2)
    (hS0 : ∀ p ∈ ManuscriptPole.ZInQ.poleS0, 4 ≤ padicValRat p B) :
    ∃ (b : Fin 6 → ℚ) (β θ : ℕ) (s c : ℚ), (∀ i, b i = 0 ∨ b i = 1) ∧ s ≠ 0 ∧ c ≠ 0 ∧
      Squarefree β ∧ Squarefree θ ∧ β % 24 = 17 ∧ θ % 24 = 1 ∧ Nat.Coprime β θ ∧
      (∀ p : ℕ, p.Prime → p ∣ θ → IsSquare (β : ZMod p)) ∧
      (∀ p : ℕ, p.Prime → p ∣ β → IsSquare (θ : ZMod p)) ∧
      ∀ A : ℚ, A = (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
        (1 + 12 * b 5) * B → A = β * s ^ 2 ∧ A * (A - B ^ 2) = θ * c ^ 2 := by
  -- `B = N / D²`
  obtain ⟨D, hD⟩ := hden
  set N := B.num.natAbs with hNdef
  have hB0 : B ≠ 0 := hpos.ne'
  have hnum : (B.num : ℚ) = N := by
    rw [hNdef, Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hpos)]
  have hDpos : 0 < D := Nat.pos_of_ne_zero (by
    rintro rfl; have := B.den_pos; rw [hD] at this; simp at this)
  have hBND : B = N / ((D : ℚ) * D) := by
    conv_lhs => rw [← Rat.num_div_den B]
    rw [hnum, hD]; push_cast; rfl
  have hcop : Nat.Coprime N D := by
    have h := B.reduced; rw [hD] at h
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_right D D) h
  have hNpos : 0 < N := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hB0)
  -- `2⁴ 3⁴ 5² 7² 13² ∣ N`
  have h4 : ∀ p ∈ ManuscriptPole.ZInQ.poleS0, p ^ 4 ∣ N := fun p hp => pow4_dvd_num (by
    simp only [ManuscriptPole.ZInQ.poleS0, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num) (hS0 p hp) hB0
  have hbig : 2730 * 2730 * 36 ∣ N := by
    have e2 := h4 2 (by decide)
    have e3 := h4 3 (by decide)
    have e5 : 5 ^ 2 ∣ N := (pow_dvd_pow 5 (by norm_num : 2 ≤ 4)).trans (h4 5 (by decide))
    have e7 : 7 ^ 2 ∣ N := (pow_dvd_pow 7 (by norm_num : 2 ≤ 4)).trans (h4 7 (by decide))
    have e13 : 13 ^ 2 ∣ N := (pow_dvd_pow 13 (by norm_num : 2 ≤ 4)).trans (h4 13 (by decide))
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) e2 e3
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this e5
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this e7
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) this e13
    norm_num at this ⊢; exact this
  obtain ⟨L, hL⟩ := hbig
  -- `D` is prime to `6`
  have hD2 : ¬ 2 ∣ D := fun h => by
    have : 2 ∣ Nat.gcd N D := Nat.dvd_gcd ⟨1365 * 2730 * 36 * L, by rw [hL]; ring⟩ h
    rw [hcop] at this; norm_num at this
  have hD3 : ¬ 3 ∣ D := fun h => by
    have : 3 ∣ Nat.gcd N D := Nat.dvd_gcd ⟨910 * 2730 * 36 * L, by rw [hL]; ring⟩ h
    rw [hcop] at this; norm_num at this
  -- `N = k² r`, `r = r₀ r₁`
  obtain ⟨k, r, hkr, hr⟩ := exists_sq_mul_squarefree N
  set r₀ := Nat.gcd r 2730 with hr₀
  set r₁ := r / r₀ with hr₁
  have hr01 : r = r₀ * r₁ := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r 2730)).symm
  have hr1cop : Nat.Coprime r₁ 2730 := by
    set g' := Nat.gcd r₁ 2730
    have hg0 : g' ∣ r₀ := Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans
      (by rw [hr01]; exact dvd_mul_left _ _)) (Nat.gcd_dvd_right _ _)
    have : g' * g' ∣ r := by rw [hr01]; exact mul_dvd_mul hg0 (Nat.gcd_dvd_left _ _)
    exact Nat.isUnit_iff.mp (hr _ this)
  have hr1_2 : ¬ 2 ∣ r₁ := fun h => by
    have := Nat.dvd_gcd h (by norm_num : 2 ∣ 2730); rw [hr1cop] at this; norm_num at this
  have hr1_3 : ¬ 3 ∣ r₁ := fun h => by
    have := Nat.dvd_gcd h (by norm_num : 3 ∣ 2730); rw [hr1cop] at this; norm_num at this
  obtain ⟨f, hfS, hf24⟩ := exists_f r₁ hr1_2 hr1_3
  have hr0d : r₀ ∈ Nat.divisors 2730 :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, by norm_num⟩
  set g := Nat.gcd r₀ f with hg
  set m := r₀ * f / g ^ 2 with hm
  obtain ⟨hmg, hm2730⟩ := m_of_r0f r₀ hr0d f hfS
  rw [← hg, ← hm] at hmg hm2730
  have hmd : m ∈ Nat.divisors 2730 := Nat.mem_divisors.mpr ⟨hm2730, by norm_num⟩
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm2730 (by norm_num)
  have hf2730 : f ∣ 2730 := fSet_dvd f hfS
  have hfpos : 0 < f := Nat.pos_of_dvd_of_pos hf2730 (by norm_num)
  have hg2730 : g ∣ 2730 := (Nat.gcd_dvd_right _ _).trans hf2730
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hg2730 (by norm_num)
  -- `β`
  set β := f * r₁ with hβ
  have hkey : m * N * g ^ 2 = β * (k * r₀) ^ 2 := by
    calc m * N * g ^ 2 = (m * g ^ 2) * N := by ring
      _ = r₀ * f * (k ^ 2 * (r₀ * r₁)) := by rw [hmg, ← hkr, hr01]
      _ = β * (k * r₀) ^ 2 := by rw [hβ]; ring
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hkr; simp at hkr; omega
    · exact h
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hkr; simp at hkr; omega
    · exact h
  have hr0pos : 0 < r₀ := Nat.gcd_pos_of_pos_left _ hrpos
  -- `N / m`
  obtain ⟨m', hm'⟩ := hm2730
  set Nm := m' * 2730 * 36 * L with hNm
  have hNNm : N = m * Nm := by
    have h' : N = 2730 * (2730 * 36 * L) := by rw [hL]; ring
    rw [h', hNm]; nth_rw 1 [hm']; ring
  have hNm24 : Nm % 24 = 0 := by
    have : 24 ∣ Nm := ⟨m' * 4095 * L, by rw [hNm]; ring⟩
    omega
  have h2730Nm : 2730 ∣ Nm := ⟨m' * 36 * L, by rw [hNm]; ring⟩
  have hNmlt : Nm < D * D := by
    have h1 : (N : ℚ) / (D * D) < 1 / 2 := hBND ▸ hlt
    have hDD : (0 : ℚ) < D * D := by positivity
    rw [div_lt_iff₀ hDD] at h1
    have : (N : ℚ) < D * D := by linarith
    have : N < D * D := by exact_mod_cast this
    have : Nm ≤ N := by rw [hNNm]; exact Nat.le_mul_of_pos_left _ hmpos
    omega
  -- `T = D² − N/m = kT² θ`
  set T := D * D - Nm with hT
  have hTNm : T + Nm = D * D := by omega
  have hDD24 := sq_mod_24 hD2 hD3
  have hT24 : T % 24 = 1 := by omega
  obtain ⟨kT, θ, hkθ, hθ⟩ := exists_sq_mul_squarefree T
  have hkT2 : ¬ 2 ∣ kT := fun h => by
    have : 2 ∣ T := by rw [← hkθ]; exact (dvd_pow h two_ne_zero).mul_right _
    omega
  have hkT3 : ¬ 3 ∣ kT := fun h => by
    have : 3 ∣ T := by rw [← hkθ]; exact (dvd_pow h two_ne_zero).mul_right _
    omega
  have hθ24 : θ % 24 = 1 := by
    have h1 := sq_mod_24 hkT2 hkT3
    have : (kT ^ 2 * θ) % 24 = 1 := by rw [hkθ]; exact hT24
    rw [Nat.mul_mod, pow_two, h1, one_mul, Nat.mod_mod] at this
    exact this
  have hkTpos : 0 < kT := by
    rcases Nat.eq_zero_or_pos kT with h | h
    · rw [h] at hkθ; simp at hkθ; omega
    · exact h
  have hm2730' : m ∣ 2730 := ⟨m', hm'⟩
  have hpNm_of : ∀ p : ℕ, p.Prime → p ∣ 2730 → p ∣ Nm := fun p _ h => h.trans h2730Nm
  -- (a) at a prime of `β`, `θ` is a nonzero square
  have hA_ : ∀ p : ℕ, p.Prime → p ∣ β → IsSquare (θ : ZMod p) ∧ ¬ p ∣ θ := by
    intro p hp hpβ
    have := Fact.mk hp
    have hpNm : p ∣ Nm := by
      by_cases hp2730 : p ∣ 2730
      · exact hpNm_of p hp hp2730
      · have hpf : ¬ p ∣ f := fun h => hp2730 (h.trans hf2730)
        have hpr1 : p ∣ r₁ := (hp.dvd_mul.mp hpβ).resolve_left hpf
        have hpN : p ∣ N := by rw [← hkr, hr01]; exact (hpr1.mul_left r₀).mul_left _
        have hpm : ¬ p ∣ m := fun h => hp2730 (h.trans hm2730')
        rw [hNNm] at hpN; exact (hp.dvd_mul.mp hpN).resolve_left hpm
    have hpN : p ∣ N := hNNm ▸ (hpNm.mul_left m)
    have hpD : ¬ p ∣ D := fun h => by
      have := Nat.dvd_gcd hpN h; rw [hcop] at this; exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hD0 : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hTNm
    rw [← hkθ] at h1; push_cast at h1
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hpNm, add_zero] at h1
    have hkT0 : (kT : ZMod p) ≠ 0 := fun h => hD0 (by
      rw [h] at h1; simp at h1; exact h1)
    have hθ0 : (θ : ZMod p) ≠ 0 := fun h => hD0 (by
      rw [h] at h1; simp at h1; exact h1)
    refine ⟨⟨D / kT, ?_⟩, fun h => hθ0 ((ZMod.natCast_eq_zero_iff _ _).mpr h)⟩
    field_simp; linear_combination h1
  -- (b) at a prime of `θ`, `β` is a square
  have hB_ : ∀ p : ℕ, p.Prime → p ∣ θ → IsSquare (β : ZMod p) := by
    intro p hp hpθ
    have := Fact.mk hp
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hTNm
    rw [← hkθ] at h1; push_cast at h1
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hpθ, mul_zero, zero_add] at h1
    have hD0 : (D : ZMod p) ≠ 0 := by
      intro h
      rw [h, mul_zero, ZMod.natCast_eq_zero_iff] at h1
      have hpN : p ∣ N := hNNm ▸ (h1.mul_left m)
      have hpD : p ∣ D := (ZMod.natCast_eq_zero_iff _ _).mp h
      have := Nat.dvd_gcd hpN hpD; rw [hcop] at this; exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hp2730 : ¬ p ∣ 2730 := fun h => hD0 (by
      have := (ZMod.natCast_eq_zero_iff _ _).mpr (hpNm_of p hp h)
      rw [this] at h1; exact mul_self_eq_zero.mp h1.symm)
    have hm0 : (m : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hp2730 (h.trans hm2730')
    have hg0 : (g : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => hp2730 (h.trans hg2730)
    have hk := congrArg (Nat.cast : ℕ → ZMod p) hkey
    rw [hNNm] at hk; push_cast at hk
    rw [h1] at hk
    have hkr0 : ((k : ZMod p) * r₀) ≠ 0 := by
      intro h
      rw [h] at hk
      have : (m : ZMod p) * (m * (D * D)) * g ^ 2 = 0 := by rw [hk]; ring
      simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        or_self] at this
      tauto
    have hk0 : (k : ZMod p) ≠ 0 := left_ne_zero_of_mul hkr0
    have hr00 : (r₀ : ZMod p) ≠ 0 := right_ne_zero_of_mul hkr0
    refine ⟨m * D * g / (k * r₀), ?_⟩
    field_simp; linear_combination -hk
  -- the bits of `m`
  have hmb := m_bits m hmd
  set bit : ℕ → ℚ := fun p => if p ∣ m then 1 else 0 with hbit
  have hmq : (1 - 2 * (0 : ℚ)) * (1 + bit 2) * (1 + 2 * bit 3) * (1 + 4 * bit 5) *
      (1 + 6 * bit 7) * (1 + 12 * bit 13) = m := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hmb
    push_cast at h
    rw [h]; simp only [hbit]; split_ifs <;> norm_num
  have hBm : B = m * Nm / ((D : ℚ) * D) := by
    rw [hBND]; congr 1; exact_mod_cast hNNm
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  refine ⟨![0, bit 2, bit 3, bit 5, bit 7, bit 13], β, θ, (k * r₀ : ℚ) / (g * D),
    (kT * m : ℚ) * B / D, ?_, ?_, ?_, ?_, hθ, ?_, hθ24, ?_, hB_, fun p hp h => (hA_ p hp h).1, ?_⟩
  · intro i; fin_cases i <;> simp [hbit] <;> omega
  · refine div_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ hD0) <;> norm_cast <;> omega
  · refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hB0) hD0 <;> norm_cast <;> omega
  · exact Nat.squarefree_mul_iff.mpr ⟨Nat.Coprime.coprime_dvd_left hf2730 hr1cop.symm,
      Squarefree.squarefree_of_dvd hf2730 squarefree_2730,
      Squarefree.squarefree_of_dvd ⟨r₀, by rw [hr01]; ring⟩ hr⟩
  · exact hf24
  · exact Nat.coprime_of_dvd (fun p hp hpβ hpθ => (hA_ p hp hpβ).2 hpθ)
  · intro A hA
    have hA' : A = (m : ℚ) * B := by rw [hA, ← hmq]; rfl
    have hk : (m : ℚ) * N * g ^ 2 = β * (k * r₀) ^ 2 := by exact_mod_cast hkey
    have hθT : (kT : ℚ) ^ 2 * θ = D * D - Nm := by
      have h := congrArg (Nat.cast : ℕ → ℚ) hTNm
      rw [← hkθ] at h; push_cast at h; linarith
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
    refine ⟨?_, ?_⟩
    · rw [hA', hBND, div_pow, mul_pow]
      field_simp
      linear_combination hk
    · have e1 : (m : ℚ) - B = m * (D * D - Nm) / (D * D) := by rw [hBm]; field_simp
      rw [hA']
      calc (m : ℚ) * B * ((m : ℚ) * B - B ^ 2) = (m : ℚ) * B ^ 2 * ((m : ℚ) - B) := by ring
        _ = θ * ((kT * m : ℚ) * B / D) ^ 2 := by rw [e1, ← hθT]; field_simp

end ZInQ.Manuscript.PoleRC
