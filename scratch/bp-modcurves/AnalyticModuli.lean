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
The other half, that every isomorphism of pairs is such a homothety, is not proved here.
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

end BPModCurves

#print axioms BPModCurves.lattice_homothety
#print axioms BPModCurves.point_preserved_iff
#print axioms BPModCurves.exactOrder
