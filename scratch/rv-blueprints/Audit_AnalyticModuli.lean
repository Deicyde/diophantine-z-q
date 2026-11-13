import Mathlib

/-!
# bp-modcurves, node MC2d: the moduli interpretation of `Γ₁(N)\ℍ` at the level of points

For `τ ∈ ℍ` let `Λ_τ = ℤτ + ℤ`. The pair `(ℂ/Λ_τ, 1/N)` is a complex elliptic curve with a point
of exact order `N`. Mathlib's `PeriodPair.weierstrassP` and `derivWeierstrassP_sq` give its
Weierstrass model `y² = 4x³ − g₂x − g₃`. For `γ = (a b; c d) ∈ SL₂(ℤ)` with `j = cτ + d`:

* `lattice_homothety` : multiplication by `j` maps `Λ_{γτ}` onto `Λ_τ`;
* `point_preserved_iff` : it maps the point `1/N` of `ℂ/Λ_{γτ}` to the point `1/N` of `ℂ/Λ_τ`
  **iff `γ ∈ Γ₁(N)`** (Mathlib's `CongruenceSubgroup.Gamma1`);
* `exactOrder` : `1/N` has exact order `N` in `ℂ/Λ_τ`.

This is the analytic half of `Y₁(N)(ℂ) = Γ₁(N)\ℍ` (Diamond–Shurman, Thm 1.5.1, UNVERIFIED number).
Below, `exists_SL2_of_homothety` and `pair_iso_iff` show that homotheties between such pairs are
exactly `Γ₁(N)`, and `exists_normalize` moves every primitive level-`N` point to `1/N`. Still open:
every lattice is some `αΛ_τ`, and every holomorphic isomorphism of tori is a homothety.
-/

namespace BPModCurves

open UpperHalfPlane CongruenceSubgroup Matrix
open scoped MatrixGroups

/-- The lattice `ℤτ + ℤ`. -/
def lat (τ : ℂ) : Set ℂ := {z | ∃ m n : ℤ, z = m * τ + n}

/-- The automorphy factor `j(γ, τ) = cτ + d`. -/
def jfac (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe; rwa [Matrix.det_fin_two] at h

theorem jfac_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : jfac γ τ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [jfac, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero,
    Complex.zero_re] at him hre
  have hc : (γ 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · exact absurd h1 τ.im_pos.ne'
  rw [hc, zero_mul, zero_add] at hre
  have hc' : γ 1 0 = 0 := by exact_mod_cast hc
  have hd' : γ 1 1 = 0 := by exact_mod_cast hre
  have := det_entries γ
  rw [hc', hd'] at this
  simp at this

theorem coe_smul_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / jfac γ τ := by
  rw [coe_specialLinearGroup_apply]
  simp [jfac]

/-- **Multiplication by `j(γ,τ)` maps `Λ_{γτ}` onto `Λ_τ`.** -/
theorem lattice_homothety (γ : SL(2, ℤ)) (τ : ℍ) :
    (fun z => jfac γ τ * z) '' lat ((γ • τ : ℍ) : ℂ) = lat τ := by
  have hj := jfac_ne_zero γ τ
  have hdet := det_entries γ
  have key : ∀ m n : ℤ, jfac γ τ * (m * ((γ • τ : ℍ) : ℂ) + n) =
      ((m * γ 0 0 + n * γ 1 0 : ℤ) : ℂ) * τ + ((m * γ 0 1 + n * γ 1 1 : ℤ) : ℂ) := by
    intro m n
    rw [coe_smul_eq]
    field_simp
    simp only [jfac]; push_cast; ring
  ext w
  constructor
  · rintro ⟨z, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨_, _, key m n⟩
  · rintro ⟨p, q, rfl⟩
    refine ⟨_, ⟨p * γ 1 1 - q * γ 1 0, -p * γ 0 1 + q * γ 0 0, rfl⟩, ?_⟩
    simp only
    rw [key]
    have e1 : (p * γ 1 1 - q * γ 1 0) * γ 0 0 + (-p * γ 0 1 + q * γ 0 0) * γ 1 0 = p := by
      linear_combination p * hdet
    have e2 : (p * γ 1 1 - q * γ 1 0) * γ 0 1 + (-p * γ 0 1 + q * γ 0 0) * γ 1 1 = q := by
      linear_combination q * hdet
    rw [e1, e2]

/-- Coefficients in `ℤτ + ℤ` are unique (`τ ∉ ℝ`). -/
theorem lat_coeff_unique (τ : ℍ) {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
  have hm : (m : ℝ) = m' := mul_right_cancel₀ τ.im_pos.ne' him
  have hm' : m = m' := by exact_mod_cast hm
  subst hm'
  have : (n : ℝ) = n' := by linarith
  exact ⟨rfl, by exact_mod_cast this⟩

/-- **The homothety by `j(γ,τ)` carries the point `1/N` to `1/N` iff `γ ∈ Γ₁(N)`.** -/
theorem point_preserved_iff (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (τ : ℍ) :
    jfac γ τ * (1 / (N : ℂ)) - 1 / (N : ℂ) ∈ lat τ ↔ γ ∈ Gamma1 N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hdet := det_entries γ
  rw [Gamma1_mem]
  constructor
  · rintro ⟨m, n, h⟩
    have h' : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 - 1 : ℤ) : ℂ) =
        ((N * m : ℤ) : ℂ) * τ + ((N * n : ℤ) : ℂ) := by
      have := congrArg (· * (N : ℂ)) h
      simp only [jfac] at this
      field_simp at this
      push_cast
      linear_combination this
    obtain ⟨hc, hd⟩ := lat_coeff_unique τ h'
    have hc0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
      rw [hc]; push_cast; simp
    have hd1 : ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have : γ 1 1 = 1 + N * n := by omega
      rw [this]; push_cast; simp
    refine ⟨?_, hd1, hc0⟩
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    push_cast at this
    rw [hd1, hc0] at this
    linear_combination this
  · rintro ⟨-, hd1, hc0⟩
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc0
    obtain ⟨m, hm⟩ := hc0
    have hd : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hd1]; ring
    obtain ⟨n, hn⟩ := hd
    refine ⟨m, n, ?_⟩
    simp only [jfac]
    have hc' : ((γ 1 0 : ℤ) : ℂ) = (N : ℂ) * m := by rw [hm]; push_cast; ring
    have hd' : ((γ 1 1 : ℤ) : ℂ) = (N : ℂ) * n + 1 := by
      have : γ 1 1 = N * n + 1 := by omega
      rw [this]; push_cast; ring
    rw [hc', hd']
    field_simp
    ring

/-- **`1/N` has exact order `N` in `ℂ/Λ_τ`**: `k · (1/N) ∈ Λ_τ ↔ N ∣ k`. -/
theorem exactOrder (N : ℕ) [NeZero N] (τ : ℍ) (k : ℤ) :
    (k : ℂ) * (1 / (N : ℂ)) ∈ lat τ ↔ (N : ℤ) ∣ k := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  constructor
  · rintro ⟨m, n, h⟩
    have h' : ((0 : ℤ) : ℂ) * τ + ((k : ℤ) : ℂ) = ((N * m : ℤ) : ℂ) * τ + ((N * n : ℤ) : ℂ) := by
      have := congrArg (· * (N : ℂ)) h
      field_simp at this
      push_cast
      linear_combination this
    obtain ⟨-, hk⟩ := lat_coeff_unique τ h'
    exact ⟨n, hk⟩
  · rintro ⟨n, rfl⟩
    refine ⟨0, n, ?_⟩
    push_cast
    field_simp
    ring

/-- **Every homothety between the lattices `Λ_{τ'}` and `Λ_τ` comes from `SL₂(ℤ)`.** -/
theorem exists_SL2_of_homothety (τ τ' : ℍ) (α : ℂ)
    (h : (fun z => α * z) '' lat (τ' : ℂ) = lat τ) :
    ∃ γ : SL(2, ℤ), (τ' : ℂ) = ((γ • τ : ℍ) : ℂ) ∧ α = jfac γ τ := by
  have hmem : ∀ w ∈ lat (τ : ℂ), ∃ m n : ℤ, w = α * (m * τ' + n) := by
    intro w hw
    rw [← h] at hw
    obtain ⟨z, ⟨m, n, rfl⟩, rfl⟩ := hw
    exact ⟨m, n, rfl⟩
  have himg : ∀ m n : ℤ, ∃ p q : ℤ, α * ((m : ℂ) * τ' + n) = (p : ℂ) * τ + q := by
    intro m n
    have : α * ((m : ℂ) * τ' + n) ∈ lat (τ : ℂ) := by
      rw [← h]; exact ⟨_, ⟨m, n, rfl⟩, rfl⟩
    obtain ⟨p, q, e⟩ := this
    exact ⟨p, q, e⟩
  obtain ⟨p, q, hpq⟩ := himg 1 0
  obtain ⟨r, s, hrs⟩ := himg 0 1
  simp only [Int.cast_one, one_mul, Int.cast_zero, add_zero, zero_mul, zero_add, mul_one] at hpq hrs
  -- `α τ' = pτ + q`, `α = rτ + s`
  obtain ⟨m₁, n₁, e₁⟩ := hmem τ ⟨1, 0, by simp⟩
  obtain ⟨m₂, n₂, e₂⟩ := hmem 1 ⟨0, 1, by simp⟩
  have e₁' : ((1 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ) =
      ((m₁ * p + n₁ * r : ℤ) : ℂ) * τ + ((m₁ * q + n₁ * s : ℤ) : ℂ) := by
    push_cast; linear_combination e₁ + m₁ * hpq + n₁ * hrs
  have e₂' : ((0 : ℤ) : ℂ) * τ + ((1 : ℤ) : ℂ) =
      ((m₂ * p + n₂ * r : ℤ) : ℂ) * τ + ((m₂ * q + n₂ * s : ℤ) : ℂ) := by
    push_cast; linear_combination e₂ + m₂ * hpq + n₂ * hrs
  obtain ⟨c11, c12⟩ := lat_coeff_unique τ e₁'
  obtain ⟨c21, c22⟩ := lat_coeff_unique τ e₂'
  have hdet1 : (m₁ * n₂ - n₁ * m₂) * (p * s - q * r) = 1 := by
    linear_combination (m₂ * q + n₂ * s) * c11.symm + c22.symm - (m₂ * p + n₂ * r) * c12.symm
  -- orientation: `p s − q r > 0`
  have hα : α ≠ 0 := by
    rintro rfl
    have := e₂; simp at this
  have hτ' : (τ' : ℂ) * ((r : ℂ) * τ + s) = (p : ℂ) * τ + q := by
    rw [← hpq, ← hrs]; ring
  have him := congrArg Complex.im hτ'
  have hre := congrArg Complex.re hτ'
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero, add_zero] at him hre
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  set x' := (τ' : ℂ).re
  set y' := (τ' : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hy' : 0 < y' := τ'.im_pos
  have key : ((p * s - q * r : ℤ) : ℝ) * y = y' * ((r * x + s) ^ 2 + (r * y) ^ 2) := by
    push_cast
    linear_combination -(r * x + s) * him + (r * y) * hre
  have hD : 0 < (r * x + s) ^ 2 + ((r : ℝ) * y) ^ 2 := by
    rcases eq_or_ne (r : ℝ) 0 with hr | hr
    · have hs : (s : ℝ) ≠ 0 := by
        intro hs
        apply hα
        rw [hrs]
        have hr0 : r = 0 := by exact_mod_cast hr
        have hs0 : s = 0 := by exact_mod_cast hs
        rw [hr0, hs0]; simp
      rw [hr]; simp; positivity
    · have : 0 < ((r : ℝ) * y) ^ 2 := by positivity
      nlinarith [sq_nonneg ((r : ℝ) * x + s)]
  have hpos : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) := by
    have := mul_pos hy' hD
    rw [← key] at this
    exact pos_of_mul_pos_left this hy.le
  have hpos' : 0 < p * s - q * r := by exact_mod_cast hpos
  have hdet : p * s - q * r = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet1 with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2
    · omega
  let γ : SL(2, ℤ) := ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  have h00 : γ 0 0 = p := rfl
  have h01 : γ 0 1 = q := rfl
  have h10 : γ 1 0 = r := rfl
  have h11 : γ 1 1 = s := rfl
  have hjf : jfac γ τ = (r : ℂ) * τ + s := by simp only [jfac, h10, h11]
  have hD0 : (r : ℂ) * τ + s ≠ 0 := by rw [← hrs]; exact hα
  refine ⟨γ, ?_, ?_⟩
  · have hγ := coe_smul_eq γ τ
    rw [hγ, hjf, h00, h01, eq_div_iff hD0]
    exact hτ'
  · rw [hjf, hrs]

/-- **Moduli at the level of points: `(ℂ/Λ_{τ'}, 1/N) ≅ (ℂ/Λ_τ, 1/N)` by a homothety iff
`τ' ∈ Γ₁(N)·τ`.** -/
theorem pair_iso_iff (N : ℕ) [NeZero N] (τ τ' : ℍ) :
    (∃ α : ℂ, (fun z => α * z) '' lat (τ' : ℂ) = lat τ ∧ α * (1 / (N : ℂ)) - 1 / (N : ℂ) ∈ lat τ) ↔
      ∃ γ ∈ Gamma1 N, τ' = γ • τ := by
  constructor
  · rintro ⟨α, hα, hpt⟩
    obtain ⟨γ, hτ', rfl⟩ := exists_SL2_of_homothety τ τ' α hα
    exact ⟨γ, (point_preserved_iff N γ τ).1 hpt, UpperHalfPlane.ext hτ'⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨jfac γ τ, lattice_homothety γ τ, (point_preserved_iff N γ τ).2 hγ⟩

/-! ### Every point `(cτ + d)/N` with `(c, d)` primitive mod `N` is equivalent to `1/N`

`lift_coprime` is copied from `Gamma1Genus.lean` (scratch files cannot import each other). -/

/-- Lifting a pair that is primitive modulo `N` to a coprime pair of naturals. -/
theorem lift_coprime (N a c : ℕ) (hN : 0 < N)
    (hprim : ∀ k, k.Prime → k ∣ N → k ∣ a → k ∣ c → False) :
    ∃ a' c' : ℕ, (a' : ZMod N) = a ∧ (c' : ZMod N) = c ∧ Nat.Coprime a' c' := by
  classical
  set c' := if c = 0 then N else c with hc'
  have hc'pos : 0 < c' := by
    rw [hc']; split_ifs with h
    · exact hN
    · omega
  have hc'mod : (c' : ZMod N) = c := by
    rw [hc']; split_ifs with h
    · simp [h]
    · rfl
  have hkc : ∀ k, k.Prime → k ∣ c' → k ∣ N → k ∣ c := by
    intro k hk h1 h2
    rw [hc'] at h1
    split_ifs at h1 with h
    · rw [h]; exact dvd_zero k
    · exact h1
  set t := ∏ p ∈ c'.primeFactors.filter (fun p => ¬ p ∣ a), p with ht
  refine ⟨a + t * N, c', by simp, hc'mod, ?_⟩
  apply Nat.coprime_of_dvd
  intro k hk hka hkc'
  by_cases hkA : k ∣ a
  · have hkt : ¬ k ∣ t := by
      intro hdvd
      rw [ht] at hdvd
      obtain ⟨p, hp, hkp⟩ := (Prime.dvd_finsetProd_iff hk.prime _).1 hdvd
      rw [Finset.mem_filter] at hp
      have : k = p := (Nat.prime_dvd_prime_iff_eq hk (Nat.prime_of_mem_primeFactors hp.1)).1 hkp
      exact hp.2 (this ▸ hkA)
    have hkN : ¬ k ∣ N := fun hkN => hprim k hk hkN hkA (hkc k hk hkc' hkN)
    have : k ∣ t * N := (Nat.dvd_add_right hkA).1 hka
    rcases (Nat.Prime.dvd_mul hk).1 this with h | h
    · exact hkt h
    · exact hkN h
  · have hkt : k ∣ t := by
      rw [ht]
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hk, hkc', hc'pos.ne'⟩, hkA⟩
    exact hkA ((Nat.dvd_add_left (dvd_mul_of_dvd_left hkt N)).1 hka)

/-- A primitive bottom row modulo `N` lifts to `SL₂(ℤ)`. -/
theorem exists_SL2_bottomRow (N : ℕ) [NeZero N] (c d : ℤ)
    (hv : ∃ x y : ZMod N, x * (c : ZMod N) + y * (d : ZMod N) = 1) :
    ∃ γ : SL(2, ℤ), (N : ℤ) ∣ γ 1 0 - c ∧ (N : ℤ) ∣ γ 1 1 - d := by
  obtain ⟨x, y, hxy⟩ := hv
  set c₀ := (c : ZMod N).val
  set d₀ := (d : ZMod N).val
  have hc₀ : ((c₀ : ℕ) : ZMod N) = c := ZMod.natCast_zmod_val _
  have hd₀ : ((d₀ : ℕ) : ZMod N) = d := ZMod.natCast_zmod_val _
  have hprim : ∀ k, k.Prime → k ∣ N → k ∣ c₀ → k ∣ d₀ → False := by
    intro k hk hkN h1 h2
    have : Fact (1 < k) := ⟨hk.one_lt⟩
    have h := congrArg (ZMod.castHom hkN (ZMod k)) hxy
    rw [map_add, map_mul, map_mul, map_one, ← hc₀, ← hd₀, map_natCast, map_natCast,
      (ZMod.natCast_eq_zero_iff _ _).2 h1, (ZMod.natCast_eq_zero_iff _ _).2 h2] at h
    simp at h
  obtain ⟨c', d', hc', hd', hcop⟩ := lift_coprime N c₀ d₀ (Nat.pos_of_ne_zero (NeZero.ne N)) hprim
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨⟨!![w, -u; (c' : ℤ), (d' : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huw
  · show (N : ℤ) ∣ (c' : ℤ) - c
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hc', hc₀]; ring
  · show (N : ℤ) ∣ (d' : ℤ) - d
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hd', hd₀]; ring

/-- **Normalization of a level-`N` point**: for `(c, d)` primitive modulo `N`, there is
`γ ∈ SL₂(ℤ)` such that the homothety by `j(γ,τ)` (an isomorphism `ℂ/Λ_{γτ} ≅ ℂ/Λ_τ`, by
`lattice_homothety`) sends `1/N` to `(cτ + d)/N`. With `pair_iso_iff` this gives
`{(ℂ/Λ_τ, P) : P = (cτ+d)/N primitive}/≅ ≃ Γ₁(N)\ℍ`. -/
theorem exists_normalize (N : ℕ) [NeZero N] (τ : ℍ) (c d : ℤ)
    (hv : ∃ x y : ZMod N, x * (c : ZMod N) + y * (d : ZMod N) = 1) :
    ∃ γ : SL(2, ℤ), jfac γ τ * (1 / (N : ℂ)) - ((c : ℂ) * τ + d) / N ∈ lat τ := by
  obtain ⟨γ, ⟨m, hm⟩, ⟨n, hn⟩⟩ := exists_SL2_bottomRow N c d hv
  refine ⟨γ, m, n, ?_⟩
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hc : ((γ 1 0 : ℤ) : ℂ) = c + N * m := by
    have : γ 1 0 = c + N * m := by omega
    rw [this]; push_cast; ring
  have hd : ((γ 1 1 : ℤ) : ℂ) = d + N * n := by
    have : γ 1 1 = d + N * n := by omega
    rw [this]; push_cast; ring
  simp only [jfac, hc, hd]
  field_simp
  ring

end BPModCurves

#print axioms BPModCurves.lattice_homothety
#print axioms BPModCurves.point_preserved_iff
#print axioms BPModCurves.exactOrder
#print axioms BPModCurves.exists_SL2_of_homothety
#print axioms BPModCurves.pair_iso_iff
#print axioms BPModCurves.exists_normalize

/-! rv-blueprints axiom audit (appended): every declaration added in this file. -/
open Lean Elab Command in
elab "#rv_audit_axioms" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (c, _) in env.constants.map₂.toList do
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    let extra := axs.filter (fun a => !std.contains a)
    if extra.size > 0 then bad := bad.push (c, extra)
  logInfo m!"rv_audit: {n} declarations; non-standard axioms in {bad.size}: {bad.toList.take 20}"
#rv_audit_axioms
