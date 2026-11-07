import ZInQKernel.Model.DivisionPolynomials.MulByN
import ZInQKernel.Model.Field.Codes

/-!
# Fixed point codes by division polynomials

Blueprint: `model/field/fixed-point-codes.md`.

For `n ≥ 1`, `ψ_n(P₀) ≠ 0` and
`ι(n) = (0, re x_n, im x_n, re y_n, im y_n)` with `x_n = x(P₀) - ψ_{n+1}(P₀)ψ_{n-1}(P₀)/ψ_n(P₀)²`
and `y_n = ψ_{2n}(P₀)/(2ψ_n(P₀)⁴)`; `ι(-n)` is `ι(n)` with its last two coordinates negated and
`ι(0) = (1, 0, 0, 0, 0)`.

The proof needs that `P₀` has infinite order (Proposition 3.1, the torsion part of the generator
certificate); here it enters as the hypothesis `¬ IsOfFinAddOrder genP0` (`iota_eq_psi`). It is
proved in `Model/Generator/InfiniteOrder.lean` (`genP0_not_isOfFinAddOrder`), and the
unconditional form is `iota_eq_psi_unconditional` (`Cleanup/FixedPointCodes.lean`). The version
`iota_eq_psi_of_ne_zero` needs only `[n]P₀ ≠ O`.
-/

namespace ZInQ

open WeierstrassCurve
open ZInQ.Syntax (psiEval)

/-- `ψ_k(P₀)`. -/
noncomputable def psiP0 (k : ℤ) : K0 := psiEval genA k genX0 genY0

/-- The abscissa `x_n = x(P₀) - ψ_{n+1}(P₀)ψ_{n-1}(P₀)/ψ_n(P₀)²` of the fixed code. -/
noncomputable def fixedX (n : ℤ) : K0 := genX0 - psiP0 (n + 1) * psiP0 (n - 1) / psiP0 n ^ 2

/-- The ordinate `y_n = ψ_{2n}(P₀)/(2ψ_n(P₀)⁴)` of the fixed code. -/
noncomputable def fixedY (n : ℤ) : K0 := psiP0 (2 * n) / (2 * psiP0 n ^ 4)

lemma genP0_eq_some : ∃ h, genP0 = Affine.Point.some genX0 genY0 h := ⟨_, rfl⟩

/-- `ι(n)` from the division polynomials, for any `n` with `[n]P₀ ≠ O`. -/
theorem iota_eq_psi_of_ne_zero {n : ℤ} (hn : n • genP0 ≠ 0) :
    psiP0 n ≠ 0 ∧ iota n = ![0, (fixedX n).re, (fixedX n).im, (fixedY n).re, (fixedY n).im] := by
  obtain ⟨h, e⟩ := genP0_eq_some
  rw [e] at hn
  obtain ⟨h1, h2⟩ := mulByN_formulas_of_charZero genA (x := genX0) (y := genY0) h n
  obtain ⟨h', e'⟩ := h2 hn
  refine ⟨fun h0 => hn (h1.mpr h0), ?_⟩
  have e'' : n • (Affine.Point.some genX0 genY0 h : genCurve.toAffine.Point) =
      Affine.Point.some (fixedX n) (fixedY n) h' := e'
  rw [iota_def, e, e'']
  rfl

/-- **Fixed point codes by division polynomials.** Assuming that `P₀` has infinite order
(Proposition 3.1): for every `n ≥ 1`, `ψ_n(P₀) ≠ 0`, `ι(n) = (0, re x_n, im x_n, re y_n, im y_n)`
and `ι(-n)` is `ι(n)` with its last two coordinates negated; and `ι(0) = (1, 0, 0, 0, 0)`. -/
theorem iota_eq_psi (hP0 : ¬ IsOfFinAddOrder genP0) :
    (∀ n : ℤ, 1 ≤ n → psiP0 n ≠ 0 ∧
      iota n = ![0, (fixedX n).re, (fixedX n).im, (fixedY n).re, (fixedY n).im] ∧
      iota (-n) = ![0, (fixedX n).re, (fixedX n).im, -(fixedY n).re, -(fixedY n).im]) ∧
    iota 0 = ![1, 0, 0, 0, 0] := by
  refine ⟨fun n hn => ?_, iota_zero⟩
  have hne : n • genP0 ≠ 0 := by
    intro h0
    apply hP0
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n, by omega, h0⟩
  obtain ⟨h1, h2⟩ := iota_eq_psi_of_ne_zero hne
  refine ⟨h1, h2, ?_⟩
  rw [iota_neg, h2]
  ext i
  fin_cases i <;> rfl

end ZInQ
