import ZInQKernel.Size.Norms.Estimates

/-!
# Substitution and renaming bounds

Blueprint: `size/norms/substitution-bounds.md`.

For `P ∈ ℤ[X_i : i ∈ I]` and `Q_i ∈ ℤ[Y_j : j ∈ J]`, the substitution `P(Q) = bind₁ Q P` has
`deg P(Q) ≤ d · deg P` and `‖P(Q)‖₁ ≤ ‖P‖₁ M^{deg P}` when `deg Q_i ≤ d` and `‖Q_i‖₁ ≤ M` for
the variables of `P` (`substitution_bounds`; the norm bound is `ZInQ.Syntax.l1_bind₁_le`). A
renaming `rename f` does not increase degree or norm (`rename_bounds`), and its norm is the sum
over the image monomials of the absolute values of the summed coefficients (`l1_rename_eq`).
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 l1_finset_sum_le l1_monomial l1_bind₁_le)

variable {σ τ : Type*}

/-- `deg P(Q) ≤ d · deg P` when `deg Q_i ≤ d` for every variable `X_i` of `P`. -/
theorem totalDegree_bind₁_le (Q : σ → MvPolynomial τ ℤ) (P : MvPolynomial σ ℤ) {d : ℕ}
    (hQ : ∀ i ∈ P.vars, (Q i).totalDegree ≤ d) : (bind₁ Q P).totalDegree ≤ d * P.totalDegree :=
  (Syntax.totalDegree_bind₁_le Q P d hQ).trans_eq (mul_comm _ _)

/-- **Substitution bounds.** If `d ≥ 1`, `M ≥ 1`, and `deg Q_i ≤ d`, `‖Q_i‖₁ ≤ M` for every
variable `X_i` of `P`, then `deg P(Q) ≤ d · deg P` and `‖P(Q)‖₁ ≤ ‖P‖₁ M^{deg P}`. -/
theorem substitution_bounds (Q : σ → MvPolynomial τ ℤ) (P : MvPolynomial σ ℤ) {d M : ℕ}
    (_hd : 1 ≤ d) (hM : 1 ≤ M) (hQ : ∀ i ∈ P.vars, (Q i).totalDegree ≤ d ∧ l1 (Q i) ≤ M) :
    (bind₁ Q P).totalDegree ≤ d * P.totalDegree ∧ l1 (bind₁ Q P) ≤ l1 P * M ^ P.totalDegree :=
  ⟨totalDegree_bind₁_le Q P fun i hi => (hQ i hi).1, l1_bind₁_le Q P hM fun i hi => (hQ i hi).2⟩

/-- A renaming does not increase the norm. -/
theorem l1_rename_le (f : σ → τ) (P : MvPolynomial σ ℤ) : l1 (rename f P) ≤ l1 P := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (l1_finset_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, l1_monomial]

/-- The norm of a renaming: the coefficients of the monomials `X^α` with the same image add,
`‖P(Y_f)‖₁ = ∑_β |∑_{α ↦ β} c_α|`. -/
theorem l1_rename_eq [DecidableEq τ] (f : σ → τ) (P : MvPolynomial σ ℤ) :
    l1 (rename f P) = ∑ β ∈ P.support.image (Finsupp.mapDomain f),
      (∑ α ∈ P.support with α.mapDomain f = β, P.coeff α).natAbs := by
  classical
  have hcoeff : ∀ β, (rename f P).coeff β =
      ∑ α ∈ P.support with α.mapDomain f = β, P.coeff α := by
    intro β
    conv_lhs => rw [P.as_sum]
    rw [map_sum, coeff_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [rename_monomial, coeff_monomial]
  have hsupp : (rename f P).support ⊆ P.support.image (Finsupp.mapDomain f) := by
    intro β hβ
    rw [mem_support_iff, hcoeff] at hβ
    obtain ⟨α, hα, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    rw [Finset.mem_filter] at hα
    exact Finset.mem_image.2 ⟨α, hα.1, hα.2⟩
  rw [Syntax.l1_eq_sum_of_subset hsupp]
  exact Finset.sum_congr rfl fun β _ => by rw [hcoeff]

/-- **Renaming bounds.** For any map `f : σ → τ`, `deg P(Y_f) ≤ deg P` and `‖P(Y_f)‖₁ ≤ ‖P‖₁`. -/
theorem rename_bounds (f : σ → τ) (P : MvPolynomial σ ℤ) :
    (rename f P).totalDegree ≤ P.totalDegree ∧ l1 (rename f P) ≤ l1 P :=
  ⟨totalDegree_rename_le f P, l1_rename_le f P⟩

end ZInQ.Size
