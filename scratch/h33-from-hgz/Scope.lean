import Mathlib

/-!
# h33-from-hgz: where `GrossZagierAlgOptCd` can be applied (compiled scope facts)

`hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd` only speaks about imaginary quadratic fields `K = ℚ(√D)` with
`D` an *odd* fundamental discriminant (`IsOddImagFundDisc D`: `D < 0`, `D ≡ 1 (mod 4)`, `D` squarefree)
satisfying the Heegner hypothesis `HeegnerHyp N D` for the level `N` of a newform of a curve
isogenous to `C_d`, `d ≡ 5 (mod 8)`.

TYZ Theorem 3.3 (`h33`) is about Heegner points on `X₀(32)` over `K_n = ℚ(√−n)`, `n ≡ 5, 7 (mod 8)`,
and about the L-value `L'(A_{d₀},1) L(A_{d₁},1)` for `n = d₀ d₁`. The facts below record, in Lean, that
(1) for `n ≡ 5 (mod 8)` the field `K_n` is never a field `ℚ(√D)` to which `hGZ` applies (its
discriminant `−4n` is even, and `−n ≡ 3 (mod 4)`), and (2) a discriminant sharing a prime with the
level never satisfies the Heegner hypothesis, so `hGZ` for `C_{d₀}` (level divisible by every prime of
`d₀`) never involves a twist `C_{d₀} ⊗ χ_D` with `p ∣ D` for `p ∣ d₀`.
-/

namespace ZInQ.H33FromHGZ

/-! Verbatim copies from `ZInQKernel/Contrib/GZDecomp/Decomp.lean` (L66, L69-70); copied because the
worktree's upstream `lean/` package (imported transitively by that module) is not built here. -/

def IsOddImagFundDisc (D : ℤ) : Prop := D < 0 ∧ D % 4 = 1 ∧ Squarefree D

/-- **Heegner hypothesis**: every prime `p ∣ N` splits in `ℚ(√D)`, i.e. `χ_D(p) = 1`. -/
def HeegnerHyp (N : ℕ) (D : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → jacobiSym (p : ℤ) D.natAbs = 1

/-- For `n ≡ 5 (mod 8)`, neither `−n` nor `−4n` is an odd imaginary fundamental discriminant: the
discriminant of `K_n = ℚ(√−n)` is `−4n`, outside the scope of `GrossZagierAlgOptCd`. -/
theorem not_oddDisc_Kn_of_five (n : ℕ) (hn : n % 8 = 5) :
    ¬ IsOddImagFundDisc (-(n : ℤ)) ∧ ¬ IsOddImagFundDisc (-4 * (n : ℤ)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2.1; omega
  · have := h.2.1; omega

/-- The Heegner hypothesis fails when a prime of the level divides the discriminant. -/
theorem not_heegnerHyp_of_common_prime {N : ℕ} {D : ℤ} {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hD : D ≠ 0) (hpD : (p : ℤ) ∣ D) : ¬ HeegnerHyp N D := by
  intro h
  have h1 := h p hp hpN
  have h0 : jacobiSym (p : ℤ) D.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff]
    refine ⟨Int.natAbs_ne_zero.2 hD, ?_⟩
    have hg : (p : ℤ).gcd (D.natAbs : ℤ) = p := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.gcd_eq_left (Int.natCast_dvd.1 hpD)
    rw [hg]; exact hp.one_lt.ne'
  rw [h0] at h1; exact zero_ne_one h1

end ZInQ.H33FromHGZ
