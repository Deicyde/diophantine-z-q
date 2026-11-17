import ZInQKernel.Contrib.CloudB3RC53.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Order

/-!
# Lane RC8 (analytic prints of Theorem 5.3): vocabulary on top of the shared blueprint

The printed analytic theorems cited in the proof of Theorem 5.3 (`hyp:RC`, 11/5 manuscript
`diophantine_zq.tex` L1005–1011; proof in Sections 7–9 and Appendices E–G) are stated in this lane
over the vocabulary of the shared top layer `ZInQ.Contrib.CloudB3RC53` (`Basic.lean` there):
`qtwist E d` (the quadratic twist `E^{(d)}`), `IsLContinuation E F` (an entire continuation of
Mathlib's `L(E, s)` from `Re s > 3/2`), `AnalyticRank E r` (`ord_{s=1} L(E, s) = r`),
`completedL N F s = N^{s/2}(2π)^{-s}Γ(s)F(s)` and `RootNumber E w` (the functional equation
`Λ(2 - s) = w Λ(s)` on `0 < Re s < 2` for some level `N > 0`). This file adds only what the prints
need beyond it:

* `qtwist_curve`: `E_ℓ^{(d)} = E_{dℓ}` (PROVED); `qtwist_Δ`, `qtwist_isElliptic` (PROVED).
* `kronecker D n`: the Kronecker symbol `(D/n) = χ_D(n)` (BFH p. 543, Hoffstein–Luo p. 435);
  `kroneckerNegOne D = sgn D = χ_D(-1)`.
* `IsFundamentalDiscriminant D`; `omega D` (number of distinct prime factors).
* `IsEntireContinuation a σ₀ F`: `F` entire and equal to `∑ aₙ n^{-s}` on `σ₀ < Re s` (for the
  L-series of newforms and their twists); `lcoeff E` (the Dirichlet coefficients of `L(E, s)`),
  `isLContinuation_iff` (PROVED).
* `RootNumberAt E N w`: `RootNumber E w` with its level `N` made explicit, needed to say "every
  prime of the conductor splits" (BFH) and for the twisted functional equation;
  `rootNumber_iff_exists_rootNumberAt` (PROVED).
* `sign_eq_one_of_central_ne_zero`, `central_eq_zero_of_sign_ne_one` (PROVED): a functional
  equation with nonzero central value has sign `+1`.

**The level `N` in `RootNumber`.** For the genuine `L(E, s)` (not identically zero: its Dirichlet
series has `a₁ = 1`) two functional equations of this shape force the same `N` and the same sign,
since `(N/N')^{1-s}` would be constant on an open set; so the `N` of a `RootNumberAt` witness is the
conductor of `E`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Complex

/-! ### Quadratic twists of the manuscript's curves -/

/-- **Twists of `E_ℓ` are curves of the family** (PROVED): `E_ℓ^{(d)} = E_{dℓ}` as Weierstrass
equations, `y² = x(x - dℓ)(x + 3dℓ)`. -/
theorem qtwist_curve (ℓ d : ℚ) : qtwist (curve ℓ) d = curve (d * ℓ) := by
  simp only [qtwist, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.mk.injEq]
  refine ⟨trivial, ?_, trivial, ?_, ?_⟩ <;> ring

/-- The discriminant of a twist (PROVED): `Δ(E^{(d)}) = d⁶ Δ(E)`. -/
theorem qtwist_Δ (E : WeierstrassCurve ℚ) (d : ℚ) : (qtwist E d).Δ = d ^ 6 * E.Δ := by
  simp only [qtwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A twist by `d ≠ 0` of an elliptic curve is an elliptic curve (PROVED). -/
theorem qtwist_isElliptic {E : WeierstrassCurve ℚ} [hE : E.IsElliptic] {d : ℚ} (hd : d ≠ 0) :
    (qtwist E d).IsElliptic :=
  ⟨by
    rw [qtwist_Δ]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hd)).mul hE.isUnit⟩

/-! ### Kronecker characters and fundamental discriminants -/

/-- The Kronecker symbol `(D/2)`: `0` for even `D`, `1` for `D ≡ ±1 (mod 8)`, `-1` for
`D ≡ ±3 (mod 8)`. -/
def kroneckerTwo (D : ℤ) : ℤ :=
  if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

/-- **The Kronecker symbol `(D/n)`** for `n ≥ 1`: completely multiplicative in `n`, equal to
`kroneckerTwo D` at `n = 2` and to the Jacobi symbol at odd `n`. For a fundamental discriminant
`D`, `n ↦ (D/n)` is the quadratic character `χ_D` of conductor `|D|` attached to `ℚ(√D)` (BFH,
Invent. Math. 102 (1990), p. 543: "`χ_D(n) = (D/n)`"; Hoffstein–Luo, MRL 4 (1997), p. 435). A
prime `p` splits in `ℚ(√D)` exactly when `(D/p) = 1`. The value at `n = 0` is never used. -/
def kronecker (D : ℤ) (n : ℕ) : ℤ :=
  kroneckerTwo D ^ n.factorization 2 * jacobiSym D (n / 2 ^ n.factorization 2)

/-- `χ_D(-1) = sgn D` (BFH p. 543: "It is known that `χ_D(-1) = sgn(D)`"). -/
def kroneckerNegOne (D : ℤ) : ℤ := Int.sign D

/-- **Fundamental discriminants** (`D ≠ 1`): squarefree `D ≡ 1 (mod 4)`, or `D = 4m` with
`m ≡ 2, 3 (mod 4)` squarefree: the discriminants of quadratic fields. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  D ≠ 1 ∧ ((D % 4 = 1 ∧ Squarefree D) ∨
    ∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m)

/-- `ω(D)`, the number of distinct prime factors of an integer. -/
def omega (D : ℤ) : ℕ := D.natAbs.primeFactors.card

/-! ### Entire continuations and explicit levels -/

/-- `F` is an **entire continuation** of the Dirichlet series `∑ aₙ n^{-s}` (Mathlib's `LSeries`)
from the half-plane `σ₀ < Re s`. -/
def IsEntireContinuation (a : ℕ → ℂ) (σ₀ : ℝ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, σ₀ < s.re → F s = LSeries a s

/-- The Dirichlet coefficients of Mathlib's `L(E, s)`, as complex numbers. -/
def lcoeff (E : WeierstrassCurve ℚ) (n : ℕ) : ℂ := (E.LFunction n : ℂ)

/-- The blueprint's `IsLContinuation E F` is `IsEntireContinuation (lcoeff E) (3/2) F` (PROVED). -/
theorem isLContinuation_iff {E : WeierstrassCurve ℚ} {F : ℂ → ℂ} :
    IsLContinuation E F ↔ IsEntireContinuation (lcoeff E) (3 / 2) F :=
  Iff.rfl

/-- **`RootNumber E w` at an explicit level `N`**: `N > 0` and some entire continuation `F` of
`L(E, s)` satisfies `Λ_N(2 - s) = w Λ_N(s)` on `0 < Re s < 2`. -/
def RootNumberAt (E : WeierstrassCurve ℚ) (N : ℕ) (w : ℤ) : Prop :=
  0 < N ∧ ∃ F : ℂ → ℂ, IsLContinuation E F ∧
    ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = (w : ℂ) * completedL N F s

/-- `RootNumber` is `RootNumberAt` at some level (PROVED). -/
theorem rootNumber_iff_exists_rootNumberAt {E : WeierstrassCurve ℚ} {w : ℤ} :
    RootNumber E w ↔ ∃ N : ℕ, RootNumberAt E N w :=
  Iff.rfl

/-! ### The sign of a functional equation with nonzero central value -/

/-- The completion factor `N^{s/2} (2π)^{-s} Γ(s)` is nonzero for `N > 0` and `Re s > 0`. -/
theorem completedL_factor_ne_zero {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  · exact fun h => hN' ((Complex.cpow_eq_zero_iff _ _).mp h).1
  · exact fun h => hpi ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- **A functional equation with nonzero central value has sign `+1`** (PROVED): if
`Λ_N(k - s) = η Λ_N(s)` on `0 < Re s < k` and `F(k/2) ≠ 0`, then `η = 1`. -/
theorem sign_eq_one_of_central_ne_zero {N k : ℕ} {F : ℂ → ℂ} {η : ℂ} (hN : 0 < N) (hk : 0 < k)
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < k → completedL N F (k - s) = η * completedL N F s)
    (hF : F ((k : ℂ) / 2) ≠ 0) : η = 1 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hre : ((k : ℂ) / 2).re = (k : ℝ) / 2 := by simp
  have h := hFE ((k : ℂ) / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hc : (k : ℂ) - (k : ℂ) / 2 = (k : ℂ) / 2 := by ring
  rw [hc] at h
  have hne : completedL N F ((k : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (completedL_factor_ne_zero hN (by rw [hre]; linarith)) hF
  have h' : (η - 1) * completedL N F ((k : ℂ) / 2) = 0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hne)

/-- **A functional equation of sign `≠ 1` forces a central zero** (PROVED). -/
theorem central_eq_zero_of_sign_ne_one {N k : ℕ} {F : ℂ → ℂ} {η : ℂ} (hN : 0 < N) (hk : 0 < k)
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < k → completedL N F (k - s) = η * completedL N F s)
    (hη : η ≠ 1) : F ((k : ℂ) / 2) = 0 := by
  by_contra hF
  exact hη (sign_eq_one_of_central_ne_zero hN hk hFE hF)

end ZInQ.Manuscript.RC.PrintsAnalytic
