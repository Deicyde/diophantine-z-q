import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The vanishing test for the central specialization of (E.4).
The arithmetic inputs are the exact rational positive cone at corank zero and
the nonzero reciprocity factor of the retained class. -/

namespace ZInQ.Manuscript.RC.AppE32Fixed

private theorem det_rows_eq_zero_iff {K : Type*} [Field K] {a w : Fin 2 → K}
    (ha : a ≠ 0) :
    Matrix.det (Matrix.of ![a, w]) = 0 ↔ ∃ c : K, w = c • a := by
  constructor
  · intro hd
    have hd' : a 0 * w 1 = a 1 * w 0 := by
      simpa [Matrix.det_fin_two, sub_eq_zero] using hd
    by_cases ha0 : a 0 = 0
    · have ha1 : a 1 ≠ 0 := by
        intro ha1
        apply ha
        funext i
        fin_cases i
        · exact ha0
        · exact ha1
      have hw0 : w 0 = 0 := by
        rw [ha0, zero_mul, eq_comm, mul_eq_zero] at hd'
        exact hd'.resolve_left ha1
      refine ⟨w 1 / a 1, ?_⟩
      funext i
      fin_cases i
      · change w 0 = (w 1 / a 1) * a 0
        rw [ha0, mul_zero, hw0]
      · change w 1 = (w 1 / a 1) * a 1
        rw [div_mul_cancel₀ _ ha1]
    · refine ⟨w 0 / a 0, ?_⟩
      funext i
      fin_cases i
      · change w 0 = (w 0 / a 0) * a 0
        rw [div_mul_cancel₀ _ ha0]
      · change w 1 = (w 0 / a 0) * a 1
        rw [div_mul_eq_mul_div, eq_div_iff ha0, mul_comm (w 1) (a 0), mul_comm (w 0) (a 1)]
        exact hd'
  · rintro ⟨c, rfl⟩
    simp [Matrix.det_fin_two]
    ring

/-- Central vanishing (tex 7532–7543, 7777–7779). In coordinates on rational
positive degree one, `a` comes from the real invariant generator, and `exp`
is projection to ordinary global degree one followed by the localized dual
exponential. Its kernel is the real line. Here `w` lifts the central retained
class, `theta` is the specialized determinant basis, and `k` is the nonzero
central reciprocity factor multiplying the normalized central value `L`.
The test works also when that value is zero. -/
theorem central_zero_iff_of_wedge {K : Type*} [Field K] [CharZero K]
    {a w : Fin 2 → K} (ha : a ≠ 0) (exp : (Fin 2 → K) →ₗ[K] K)
    (hker : LinearMap.ker exp = Submodule.span K {a})
    {u theta k L : K} (hθ : theta ≠ 0) (hk : k ≠ 0)
    (hwedge : u * theta = 2 * Matrix.det (Matrix.of ![a, w]))
    (hrec : exp w = k * L) : u = 0 ↔ L = 0 := by
  have hdet : u = 0 ↔ Matrix.det (Matrix.of ![a, w]) = 0 := by
    rw [← (mul_eq_zero_iff_right hθ : u * theta = 0 ↔ u = 0), hwedge]
    exact mul_eq_zero_iff_left two_ne_zero
  have hexp : Matrix.det (Matrix.of ![a, w]) = 0 ↔ exp w = 0 := by
    rw [← LinearMap.mem_ker, hker, Submodule.mem_span_singleton]
    exact (det_rows_eq_zero_iff ha).trans (exists_congr fun c => eq_comm)
  rw [hdet, hexp, hrec]
  exact mul_eq_zero_iff_left hk


end ZInQ.Manuscript.RC.AppE32Fixed
