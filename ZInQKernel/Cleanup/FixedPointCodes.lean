import ZInQKernel.Model.DivisionPolynomials.FixedPointCodes
import ZInQKernel.Assembly.Real.Accumulation
import ZInQKernel.Model.Generator.InfiniteOrder

/-!
# Unconditional fixed point codes and real accumulation

Blueprint: `model/field/fixed-point-codes.md` and `assembly/approximation/real-accumulation.md`.

`ZInQ.iota_eq_psi` and `ZInQ.Assembly.exists_multiple_large` take the infinite order of `P₀`
as a hypothesis; it is proved (`genP0_not_isOfFinAddOrder`), so both hold unconditionally.
-/

namespace ZInQ

/-- **Fixed point codes by division polynomials.** For every `n ≥ 1`, `ψ_n(P₀) ≠ 0`,
`ι(n) = (0, re x_n, im x_n, re y_n, im y_n)` and `ι(-n)` is `ι(n)` with its last two coordinates
negated; and `ι(0) = (1, 0, 0, 0, 0)`. -/
theorem iota_eq_psi_unconditional :
    (∀ n : ℤ, 1 ≤ n → psiP0 n ≠ 0 ∧
      iota n = ![0, (fixedX n).re, (fixedX n).im, (fixedY n).re, (fixedY n).im] ∧
      iota (-n) = ![0, (fixedX n).re, (fixedX n).im, -(fixedY n).re, -(fixedY n).im]) ∧
    iota 0 = ![1, 0, 0, 0, 0] :=
  iota_eq_psi genP0_not_isOfFinAddOrder

namespace Assembly

/-- **Multiples of the generator approach the identity at both real places.** For every
`M ∈ ℝ` there is `k ≥ 1` such that `[k]P₀ = (x_k, y_k)` is affine with `σ₊(x_k) > M` and
`σ₋(x_k) > M`. -/
theorem exists_multiple_large_unconditional (M : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ (x y : K0) (h : genCurve.toAffine.Nonsingular x y),
      (k : ℤ) • genP0 = .some x y h ∧ M < K0.embPlus x ∧ M < K0.embMinus x :=
  exists_multiple_large genP0_not_isOfFinAddOrder M

end Assembly

end ZInQ
