import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: the smoothing integers (K5)–(K6) and the central normalization (K14)

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, Proposition `ex:app-kato-system`, proof
paragraphs 2 and 6 (tex 6931–6951, 7108–7204), and Section 7.1 (tex 1894–1910).

* (K5) (tex 6935): one smoothing choice `c = d_s = 1 + 2^e · 3 N_odd F` for the whole family, with
  the congruences of tex 1895–1897 and 6937–6939 (`smoothing_*`).
* (K6) (tex 6943–6946): the central scalar `s_F = (c² − c)(d_s² − d_s) = c(c − 1) d_s(d_s − 1)` has
  `v₂(s_F) = 2e`, independent of `F` (`padicValNat_sF_smoothing`).
* (K14) (tex 7144–7187): with `Ω⁻ = i|Ω⁻|` and `√h = i√|h|` for `h < 0`,
  `L(E^h, 1)/(Ω^ε √h) = L_*(h)/h` exactly, signs included (`K14_normalization`); the varying
  scalar `1/h` is a two-adic unit (`padicValRat_inv_odd`); the Gauss-basis change costs the fixed
  ratio `√(Δ_h/h) ∈ {±1, ±2}` (`gaussRatio_sq`).

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Even

/-! ## (K5) The retained smoothing integer -/

/-- **(K5)** (tex 6935): the smoothing integers `c = d_s = 1 + 2^e · 3 N_odd F`. -/
def smoothing (e Nodd F : ℕ) : ℕ := 1 + 2 ^ e * (3 * Nodd * F)

/-- `c, d_s > 1` (tex 6937: "These integers exceed one"; PROVED). -/
theorem one_lt_smoothing {e Nodd F : ℕ} (hN : 0 < Nodd) (hF : 0 < F) :
    1 < smoothing e Nodd F := by
  unfold smoothing
  have : 0 < 2 ^ e * (3 * Nodd * F) := by positivity
  omega

/-- Helper: `1 + m ≡ 1 (mod n)` whenever `n ∣ m`. -/
theorem one_add_modEq_one_of_dvd {n m : ℕ} (h : n ∣ m) : 1 + m ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.add_left 1 (Nat.modEq_zero_iff_dvd.mpr h)

/-- `c, d_s ≡ 1 (mod 3 N_odd F)` (tex 1896; PROVED). -/
theorem smoothing_modEq_one (e Nodd F : ℕ) : smoothing e Nodd F ≡ 1 [MOD 3 * Nodd * F] :=
  one_add_modEq_one_of_dvd (Dvd.intro_left _ rfl)

/-- `c, d_s ≡ 1 + 2^e (mod 2^{e+1})` (tex 1897; PROVED), for odd `N_odd`, `F`. -/
theorem smoothing_modEq_dyadic (e : ℕ) {Nodd F : ℕ} (hN : Odd Nodd) (hF : Odd F) :
    smoothing e Nodd F ≡ 1 + 2 ^ e [MOD 2 ^ (e + 1)] := by
  obtain ⟨k, hk⟩ : Odd (3 * Nodd * F) := (Nat.odd_mul.mpr ⟨by decide, hN⟩).mul hF
  unfold smoothing
  rw [hk, show 1 + 2 ^ e * (2 * k + 1) = 1 + 2 ^ e + k * 2 ^ (e + 1) by ring]
  exact Nat.add_mul_mod_self_right _ _ _

/-- `c, d_s ≡ 1 (mod N)` for `N = 2^v N_odd` with `v ≤ e` (tex 6938, `e ≥ v₂(N)`; PROVED). -/
theorem smoothing_modEq_one_level {e v : ℕ} (Nodd F : ℕ) (hv : v ≤ e) :
    smoothing e Nodd F ≡ 1 [MOD 2 ^ v * Nodd] :=
  one_add_modEq_one_of_dvd (mul_dvd_mul (pow_dvd_pow 2 hv) ⟨3 * F, by ring⟩)

/-- `c, d_s ≡ 1` modulo every dyadic quadratic conductor (`4` and `8`) once `e ≥ 3`
(tex 6938–6939; PROVED). -/
theorem smoothing_modEq_one_eight {e : ℕ} (Nodd F : ℕ) (he : 3 ≤ e) :
    smoothing e Nodd F ≡ 1 [MOD 8] :=
  one_add_modEq_one_of_dvd (Dvd.dvd.mul_right (pow_dvd_pow 2 he : 2 ^ 3 ∣ 2 ^ e) _)

/-- Helper: `1 + m` is prime to every divisor `n` of `m`. -/
theorem coprime_one_add_of_dvd {n m : ℕ} (h : n ∣ m) : Nat.Coprime (1 + m) n := by
  obtain ⟨k, rfl⟩ := h
  exact (Nat.coprime_add_mul_left_left 1 n k).mpr (Nat.coprime_one_left n)

/-- `c, d_s` are prime to `6 N F` for `N = 2^v N_odd`, `e ≥ 1` (tex 6937; PROVED). -/
theorem smoothing_coprime {e v : ℕ} {Nodd F : ℕ} (he : 1 ≤ e) :
    Nat.Coprime (smoothing e Nodd F) (6 * (2 ^ v * Nodd) * F) := by
  unfold smoothing
  have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have h6 : Nat.Coprime (1 + 2 ^ e * (3 * Nodd * F)) 6 :=
    coprime_one_add_of_dvd (show 2 * 3 ∣ 2 ^ e * (3 * Nodd * F) from
      mul_dvd_mul h2 (Dvd.dvd.mul_right (Dvd.intro _ rfl) _))
  have hc2 : Nat.Coprime (1 + 2 ^ e * (3 * Nodd * F)) 2 :=
    coprime_one_add_of_dvd (Dvd.dvd.mul_right h2 _)
  have hN : Nat.Coprime (1 + 2 ^ e * (3 * Nodd * F)) Nodd :=
    coprime_one_add_of_dvd (Dvd.dvd.mul_left ⟨3 * F, by ring⟩ _)
  have hF : Nat.Coprime (1 + 2 ^ e * (3 * Nodd * F)) F :=
    coprime_one_add_of_dvd (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _)
  exact (h6.mul_right ((hc2.pow_right v).mul_right hN)).mul_right hF

/-! ## (K6) The central scalar -/

/-- **(K6)** (tex 6944): `s_F = (c² − c)(d_s² − d_s)`. -/
def sF (c d : ℕ) : ℕ := (c ^ 2 - c) * (d ^ 2 - d)

/-- `s_F = c(c − 1) d_s(d_s − 1)` (tex 6944; PROVED). -/
theorem sF_eq (c d : ℕ) : sF c d = c * (c - 1) * (d * (d - 1)) := by
  unfold sF
  rw [sq, sq, Nat.mul_sub_one, Nat.mul_sub_one]

/-- For odd `c, d_s > 1`, `v₂(s_F) = v₂(c − 1) + v₂(d_s − 1)` (PROVED). -/
theorem padicValNat_sF {c d : ℕ} (hc : Odd c) (hd : Odd d) (hc1 : 1 < c) (hd1 : 1 < d) :
    padicValNat 2 (sF c d) = padicValNat 2 (c - 1) + padicValNat 2 (d - 1) := by
  have hc0 : padicValNat 2 c = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h))
  have hd0 : padicValNat 2 d = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr h))
  have hc' : c - 1 ≠ 0 := by omega
  have hd' : d - 1 ≠ 0 := by omega
  rw [sF_eq, padicValNat.mul (mul_ne_zero (by omega) hc') (mul_ne_zero (by omega) hd'),
    padicValNat.mul (by omega) hc', padicValNat.mul (by omega) hd', hc0, hd0, zero_add, zero_add]

/-- **(K6): `v₂(s_F) = 2e`** for `c = d_s = 1 + 2^e · 3 N_odd F` with `N_odd`, `F` odd, independent
of `F` (tex 6945–6946, 1902–1903: "Kato's explicit reciprocity formula therefore contributes
valuation `2e`, independent of `F`"; PROVED). -/
theorem padicValNat_sF_smoothing {e : ℕ} {Nodd F : ℕ} (he : 1 ≤ e) (hN : Odd Nodd) (hF : Odd F) :
    padicValNat 2 (sF (smoothing e Nodd F) (smoothing e Nodd F)) = 2 * e := by
  have hm : Odd (3 * Nodd * F) := (Nat.odd_mul.mpr ⟨by decide, hN⟩).mul hF
  have hm0 : 3 * Nodd * F ≠ 0 := by rintro h; rw [h] at hm; exact absurd hm (by decide)
  have hc : Odd (smoothing e Nodd F) := by
    unfold smoothing
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    exact ⟨k * (3 * Nodd * F), by rw [hk]; ring⟩
  have hc1 : 1 < smoothing e Nodd F := by
    unfold smoothing
    have : 0 < 2 ^ e * (3 * Nodd * F) := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hm0)
    omega
  have hv : padicValNat 2 (smoothing e Nodd F - 1) = e := by
    have hm2 : padicValNat 2 (3 * Nodd * F) = 0 :=
      padicValNat.eq_zero_of_not_dvd
        (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))
    unfold smoothing
    rw [Nat.add_sub_cancel_left, padicValNat.mul (by positivity) hm0, padicValNat.prime_pow, hm2,
      add_zero]
  rw [padicValNat_sF hc hc hc1 hc1, hv]
  ring

/-! ## (K14) The signed central normalization -/

/-- `√h` for a nonzero integer `h`, with the convention `√h = i√|h|` for `h < 0` (tex 7146). -/
noncomputable def sqrtSigned (h : ℤ) : ℂ :=
  if 0 < h then (Real.sqrt h : ℂ) else Complex.I * (Real.sqrt (-h : ℝ) : ℂ)

/-- The period on the Betti line of sign `ε = sign h`: `Ω⁺ = |Ω⁺|` for `h > 0` and
`Ω⁻ = i|Ω⁻|` for `h < 0` (tex 7146). Here `Ωp = |Ω⁺|`, `Ωm = |Ω⁻|`. -/
noncomputable def periodSigned (h : ℤ) (Ωp Ωm : ℝ) : ℂ :=
  if 0 < h then (Ωp : ℂ) else Complex.I * (Ωm : ℂ)

/-- **`L_*(h) = √|h| L(E^h, 1)/|Ω^ε|`** (tex 7175–7177), the real-period normalization, with
`L = L(E^h, 1)` (a real number) and `Ωp = |Ω⁺|`, `Ωm = |Ω⁻|`. -/
noncomputable def LstarOf (h : ℤ) (L Ωp Ωm : ℝ) : ℝ :=
  Real.sqrt |(h : ℝ)| * L / (if 0 < h then Ωp else Ωm)

/-- **(K14), the signed factor** (tex 7178–7187: "This proves the signed factor in (K14), not
only its valuation"; PROVED): `L(E^h,1)/(Ω^ε √h) = L_*(h)/h`, for both signs of `h`. -/
theorem K14_normalization (h : ℤ) (hh : h ≠ 0) (L Ωp Ωm : ℝ) (hp : 0 < Ωp) (hm : 0 < Ωm) :
    (L : ℂ) / (periodSigned h Ωp Ωm * sqrtSigned h) = (LstarOf h L Ωp Ωm : ℂ) / (h : ℂ) := by
  unfold periodSigned sqrtSigned LstarOf
  have hhC : (h : ℂ) = ((h : ℝ) : ℂ) := (Complex.ofReal_intCast h).symm
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have h0 : ¬ (0 < h) := not_lt.mpr hneg.le
    simp only [h0, ↓reduceIte]
    have hr : (h : ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hr]
    set r := Real.sqrt (-(h : ℝ)) with hr_def
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hrsq : r * r = -(h : ℝ) := Real.mul_self_sqrt (by linarith)
    have hh' : (h : ℝ) = -(r * r) := by linarith
    rw [hhC, hh']
    have hr0C : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hmC : (Ωm : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    linear_combination (L : ℂ) * Complex.I_sq
  · simp only [hpos, ↓reduceIte]
    have hr : (0 : ℝ) < h := by exact_mod_cast hpos
    rw [abs_of_pos hr]
    set r := Real.sqrt (h : ℝ) with hr_def
    have hr0 : 0 < r := Real.sqrt_pos.mpr hr
    have hrsq : r * r = (h : ℝ) := Real.mul_self_sqrt hr.le
    rw [hhC, ← hrsq]
    have hr0C : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hpC : (Ωp : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    push_cast
    field_simp

/-- **The varying scalar `1/h` is a two-adic unit** for odd `h` (tex 1906, 7154; PROVED). -/
theorem padicValRat_inv_odd {h : ℤ} (hh : Odd h) : padicValRat 2 (1 / (h : ℚ)) = 0 := by
  rw [one_div, padicValRat.inv, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  · simp
  · rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hh
    omega

/-- **The Gauss-basis ratio** (tex 7155–7161, 7188–7193; PROVED): for the field discriminant
`Δ_h ∈ {h, 4h}` of `ℚ(√h)` (`h` odd squarefree), `(τ(χ)/√h)² = Δ_h/h ∈ {1, 4}`; so the ratio is
one or two up to sign, with two-adic valuation `0` or `1`, whatever the number of odd conductor
primes. (Here `ρ` stands for `τ(χ)/√h`, with `τ(χ)² = Δ_h` and `(√h)² = h`.) -/
theorem gaussRatio_sq {h Δ : ℤ} (hh : h ≠ 0) (hΔ : Δ = h ∨ Δ = 4 * h) {ρ τ s : ℂ}
    (hτ : τ ^ 2 = Δ) (hs : s ^ 2 = h) (hρ : ρ = τ / s) :
    ρ = 1 ∨ ρ = -1 ∨ ρ = 2 ∨ ρ = -2 := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hρ2 : ρ ^ 2 = (Δ : ℂ) / (h : ℂ) := by rw [hρ, div_pow, hτ, hs]
  rcases hΔ with rfl | rfl
  · rw [div_self hhC] at hρ2
    have : (ρ - 1) * (ρ + 1) = 0 := by linear_combination hρ2
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linear_combination h1
    · right; left; linear_combination h1
  · push_cast at hρ2
    rw [mul_div_assoc, div_self hhC, mul_one] at hρ2
    have : (ρ - 2) * (ρ + 2) = 0 := by linear_combination hρ2
    rcases mul_eq_zero.mp this with h1 | h1
    · right; right; left; linear_combination h1
    · right; right; right; linear_combination h1

end ZInQ.Manuscript.RC.Even
