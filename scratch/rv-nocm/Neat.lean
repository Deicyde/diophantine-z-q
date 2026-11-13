import Mathlib

/-!
# rv-nocm: the level-3 congruence subgroup of `𝒪^×` is torsion-free (neatness input of A5)

Input of `RvNocm.ramification_eq_orbifold_order` (`OrbifoldIndex.lean`) for `Y₃ → P¹_j`: the group
`Γ₃` (the image of `𝒪¹ ∩ K₃`) has no torsion. Here, for `B = (2,−3) = ℍ[ℚ, 2, 0, −3]` and
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` (coordinates `comb n`, as in `scratch/glue-repo/A1Quaternion.lean`,
whose definitions and `norm_descent` are copied below): if `x = 1 + 3y` with `y ∈ 𝒪` and
`x^m = 1` for some `m > 0`, then `y = 0`. In particular `−1 ∉ 1 + 3𝒪` and `Γ₃` is torsion-free.

Proof: `ν = nrd x` satisfies `ν^m = 1` and `ν ≡ 1 (mod 3)`, so `ν = 1`; then `t = trd x = 2 − 9K`
with `K = nrd y ∈ ℤ`. If `K = 0`, `y = 0` because the norm form is anisotropic. If `K ≠ 0`,
`|t| ≥ 7`, and `x^(j+1) = p_{j+1} x − p_j` with `|p_j|` strictly increasing (Cayley–Hamilton),
so `x^m = 1` forces `x ∈ ℚ`, hence `y ∈ ℤ`, and then `2y = −3y²` gives `y = 0`.
-/

open Quaternion

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat
  QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace RvNocm.Neat

abbrev B := ℍ[ℚ, 2, 0, -3]

/-- `n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+ij)/2` (copied from glue-repo `A1Quaternion.lean`). -/
def comb (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + n 2 / 2, n 1 + n 3 / 2, n 2 / 2, n 3 / 2⟩

/-- Reduced norm (copied). -/
def nrd (x : B) : ℚ := (x * star x).re

theorem nrd_eq (x : B) : nrd x = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
  simp [nrd]; ring

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd_eq]; simp; ring

/-- `X₀² − 2X₁² + 3X₂² − 6X₃² = 0` has only the trivial integer solution (3-adic descent). -/
theorem norm_descent : ∀ (n : ℕ) (a b c d : ℤ), a.natAbs + b.natAbs + c.natAbs + d.natAbs = n →
    a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c d hn h
    have k1 : ∀ a b c d : ZMod 3, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
        a = 0 ∧ b = 0 := by decide
    have h3 := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at h3
    obtain ⟨ha, hb⟩ := k1 _ _ _ _ h3
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    have h' : c ^ 2 - 2 * d ^ 2 + 3 * a' ^ 2 - 6 * b' ^ 2 = 0 := by push_cast at h; linarith
    have h3' := congrArg (fun z : ℤ => (z : ZMod 3)) h'
    push_cast at h3'
    obtain ⟨hc, hd⟩ := k1 _ _ _ _ h3'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc hd
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨d', rfl⟩ := hd
    by_cases h0 : a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h0; simp
    · exfalso
      have hpos : 0 < a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs := by
        by_contra hz
        apply h0
        omega
      have := ih (a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs)
        (by rw [← hn]; simp only [Int.natAbs_mul]; norm_num; omega) a' b' c' d' rfl
        (by push_cast at h'; linarith)
      exact h0 this


theorem nrd_pow (x : B) (m : ℕ) : nrd (x ^ m) = nrd x ^ m := by
  induction m with
  | zero => simp [nrd_eq]
  | succ m ih => rw [pow_succ, nrd_mul, ih, pow_succ]

/-- The integral norm form of `𝒪` in the coordinates `n`. -/
def normInt (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrd_comb (n : Fin 4 → ℤ) : nrd (comb n) = normInt n := by
  simp [nrd_eq, comb, normInt]; ring

theorem comb_eq_zero_of_normInt (n : Fin 4 → ℤ) (h : normInt n = 0) : comb n = 0 := by
  have key : (2 * n 0 + n 2) ^ 2 - 2 * (2 * n 1 + n 3) ^ 2 + 3 * n 2 ^ 2 - 6 * n 3 ^ 2 = 0 := by
    simp only [normInt] at h; linear_combination 4 * h
  obtain ⟨h0, h1, h2, h3⟩ := norm_descent _ _ _ _ _ rfl key
  have e2 : n 2 = 0 := h2
  have e3 : n 3 = 0 := h3
  have e0 : n 0 = 0 := by omega
  have e1 : n 1 = 0 := by omega
  ext <;> simp [comb, e0, e1, e2, e3]

/-- Cayley–Hamilton with integer trace and norm one: `x² = t x − 1`. -/
theorem cayley_hamilton (x : B) (t : ℤ) (ht : 2 * x.re = t) (hn : nrd x = 1) :
    x * x = t • x - 1 := by
  rw [nrd_eq] at hn
  ext <;> simp [zsmul_eq_mul] <;> [linear_combination (-1 : ℚ) * hn + x.re * ht; skip; skip; skip]
  all_goals rw [← ht]; ring

/-- The sequence `p₀ = 0`, `p₁ = 1`, `p_{j+2} = t p_{j+1} − p_j`. -/
def pseq (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (j + 2) => t * pseq t (j + 1) - pseq t j

theorem pow_formula (x : B) (t : ℤ) (hx : x * x = t • x - 1) (j : ℕ) :
    x ^ (j + 1) = pseq t (j + 1) • x - pseq t j • (1 : B) := by
  induction j with
  | zero => simp [pseq]
  | succ j ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, hx, one_mul, smul_sub, smul_smul]
    simp only [pseq]
    rw [sub_smul, mul_comm]
    abel

theorem pseq_growth (t : ℤ) (ht : 3 ≤ |t|) (j : ℕ) : |pseq t j| < |pseq t (j + 1)| := by
  induction j with
  | zero => simp [pseq]
  | succ j ih =>
    show |pseq t (j + 1)| < |t * pseq t (j + 1) - pseq t j|
    have h1 : |t * pseq t (j + 1)| - |pseq t j| ≤ |t * pseq t (j + 1) - pseq t j| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul] at h1
    have h0 : 0 ≤ |pseq t (j + 1)| := abs_nonneg _
    nlinarith

theorem pseq_ne_zero (t : ℤ) (ht : 3 ≤ |t|) (j : ℕ) : pseq t (j + 1) ≠ 0 := by
  have : ∀ j : ℕ, (j : ℤ) ≤ |pseq t j| := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => have := pseq_growth t ht j; push_cast; omega
  have := this (j + 1)
  intro h; rw [h, abs_zero] at this; omega

/-- **Neatness of level 3.** `1 + 3𝒪` contains no nontrivial element of finite order of `B^×`. -/
theorem eq_zero_of_pow_eq_one (n : Fin 4 → ℤ) {m : ℕ} (hm : 0 < m)
    (h : (1 + 3 * comb n) ^ m = 1) : comb n = 0 := by
  set y := comb n with hy
  set x : B := 1 + 3 * y with hxdef
  -- the norm
  have hν : nrd x = 1 + 3 * (2 * n 0 + n 2) + 9 * normInt n := by
    rw [← nrd_comb]; simp only [hxdef, nrd_eq, hy, comb]; simp; ring
  have hνm : nrd x ^ m = 1 := by rw [← nrd_pow, h]; simp [nrd_eq]
  have habs : |nrd x| = 1 := by
    have : |nrd x| ^ m = 1 := by rw [← abs_pow, hνm, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm.ne').mp this
  have hν1 : nrd x = 1 := by
    rcases abs_eq (zero_le_one) |>.mp habs with h1 | h1
    · exact h1
    · exfalso
      rw [hν] at h1
      have hq : ((3 * (2 * n 0 + n 2) + 9 * normInt n : ℤ) : ℚ) = -2 := by push_cast; linarith
      have : (3 * (2 * n 0 + n 2) + 9 * normInt n : ℤ) = -2 := by exact_mod_cast hq
      omega
  have hsum : 3 * (2 * n 0 + n 2) + 9 * normInt n = 0 := by
    have : ((3 * (2 * n 0 + n 2) + 9 * normInt n : ℤ) : ℚ) = 0 := by push_cast; linarith
    exact_mod_cast this
  by_cases hK : normInt n = 0
  · exact comb_eq_zero_of_normInt n hK
  · -- trace `t = 2 − 9K`
    set t : ℤ := 2 - 9 * normInt n with htdef
    have htr : 2 * x.re = t := by
      simp only [hxdef, hy, comb, htdef]; simp
      have : ((2 * n 0 + n 2 : ℤ) : ℚ) = -3 * normInt n := by
        have h' : 2 * n 0 + n 2 = -3 * normInt n := by omega
        exact_mod_cast h'
      push_cast at this; linarith
    have ht3 : 3 ≤ |t| := by
      rcases lt_or_gt_of_ne hK with hlt | hgt
      · rw [abs_of_pos (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    have hch := cayley_hamilton x t htr hν1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hp := pow_formula x t hch j
    rw [h] at hp
    have hne := pseq_ne_zero t ht3 j
    have hI := congrArg QuaternionAlgebra.imI hp
    have hJ := congrArg QuaternionAlgebra.imJ hp
    have hK' := congrArg QuaternionAlgebra.imK hp
    simp [hxdef, hy, comb, zsmul_eq_mul] at hI hJ hK'
    have e3' : n 3 = 0 := by
      rcases hK' with h | h
      · exact absurd h hne
      · exact h
    have e2' : n 2 = 0 := by
      rcases hJ with h | h
      · exact absurd h hne
      · exact h
    have e1' : n 1 = 0 := by
      rcases hI with h | h
      · exact absurd h hne
      · have h3q : (n 3 : ℚ) = 0 := by exact_mod_cast e3'
        have : (n 1 : ℚ) = 0 := by
          rw [h3q] at h; simpa using h
        exact_mod_cast this
    simp only [normInt, e1', e2', e3'] at hsum hK
    have : n 0 * (2 + 3 * n 0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by simp [h0]) hK
    · omega

end RvNocm.Neat

#print axioms RvNocm.Neat.eq_zero_of_pow_eq_one
