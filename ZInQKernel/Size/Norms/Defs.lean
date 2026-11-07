import ZInQKernel.Syntax.Language.Size

/-!
# Coefficient norms and degrees

Blueprint: `size/norms/l1-norm.md`.

The coefficient ℓ¹ norm `‖f‖₁ = ∑_α |c_α|` of an integer polynomial is `ZInQ.Syntax.l1`
(`ZInQKernel/Syntax/Language/Size.lean`), and its degree is Mathlib's `MvPolynomial.totalDegree`
(with `deg 0 = 0`). Elements `a + b s` of `S[s] = S[t]/(t² - 2)`, `S = ℤ[X_i : i ∈ I]`, are the
pairs `QuadraticAlgebra S 2 0` (`(a, b)(c, d) = (ac + 2bd, ad + bc)`); they carry the weighted
norm `‖a + b s‖ = ‖a‖₁ + 2‖b‖₁` (`pairNorm`) and the degree `max (deg a) (deg b)` (`pairDeg`).
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1)

variable {σ : Type*}

/-- `S[s] = S[t]/(t² - 2)` over `S = ℤ[X_i : i ∈ σ]`: pairs `a + b s`. -/
abbrev PairRing (σ : Type*) : Type _ := QuadraticAlgebra (MvPolynomial σ ℤ) 2 0

/-- The coefficient ℓ¹ norm `‖f‖₁ = ∑_α |c_α|`, a natural number. -/
theorem l1_def (f : MvPolynomial σ ℤ) : l1 f = ∑ α ∈ f.support, (f.coeff α).natAbs := rfl

/-- The weighted pair norm `‖a + b s‖ = ‖a‖₁ + 2‖b‖₁`. -/
def pairNorm (u : PairRing σ) : ℕ := l1 u.re + 2 * l1 u.im

/-- The degree `deg (a + b s) = max (deg a) (deg b)`. -/
noncomputable def pairDeg (u : PairRing σ) : ℕ := max u.re.totalDegree u.im.totalDegree

theorem pairNorm_def (u : PairRing σ) : pairNorm u = l1 u.re + 2 * l1 u.im := rfl

theorem pairDeg_def (u : PairRing σ) : pairDeg u = max u.re.totalDegree u.im.totalDegree := rfl

end ZInQ.Size
