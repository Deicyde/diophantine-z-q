import ZInQKernel.Assembly.Local.FormalMultiplication

/-!
# Multiplication in a formal neighbourhood (the part used here)

Blueprint: `assembly/local-tests/formal-multiplication.md`, item 3, in the form the
formal-multiple argument uses it.

Let `v : AddValuation K (WithTop ℤ)`, `A ∈ K` with `v(A) ≥ 0`, `W : y² = x³ + A x`, and `W_k`
the subgroup of points with `v(z) ≥ k` (`ZInQ.Mult.formalFilt`). If `v(q) = e` with
`0 ≤ e ≤ 4`, then `[qᵃ n] W_k ⊆ W_{k + a e}` (`nsmul_mem_formalFilt_of_val`; for `k ≤ 1` read
`W_k = W₁`). This is `ZInQ.Assembly.zsmul_mem_formalFilt_of_vge` at the level `v(z(Q)) ≥ 1`
of the point, iterated.
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult

variable {K : Type*} [Field K] [DecidableEq K] {v : AddValuation K (WithTop ℤ)} {A : K}

/-- **Item 3, one step.** If `v(q) = e` with `0 ≤ e ≤ 4`, then `[q] W_k ⊆ W_{k + e}`. -/
theorem nsmul_mem_formalFilt_add (hA : 0 ≤ v A) {k : ℤ} {q : ℕ} {e : ℤ}
    (hq : v (q : K) = e) (he0 : 0 ≤ e) (he4 : e ≤ 4) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) : q • Q ∈ formalFilt A hA (k + e) := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, nsmul_zero]; exact (formalFilt A hA (k + e)).zero_mem
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA h hQ.1
  have hkN : k ≤ N := by have := hQ.2; rw [hz] at this; exact_mod_cast this
  have hQN : Point.some x y h ∈ formalFilt A hA N := ⟨hQ.1, by rw [hz]⟩
  have hqN := Assembly.zsmul_mem_formalFilt_of_vge hA hQN (n := q) (e := e)
    (by rw [Int.cast_natCast]; exact Vge.of_eq hq)
  rw [min_eq_left (by omega), natCast_zsmul] at hqN
  exact formalFilt_antitone hA (by omega) hqN

/-- **Item 3.** If `v(q) = e` with `0 ≤ e ≤ 4`, then `[qᵃ n] W_k ⊆ W_{k + a e}`. -/
theorem nsmul_mem_formalFilt_of_val (hA : 0 ≤ v A) {k : ℤ} {q : ℕ} {e : ℤ}
    (hq : v (q : K) = e) (he0 : 0 ≤ e) (he4 : e ≤ 4) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) (a n : ℕ) : (q ^ a * n) • Q ∈ formalFilt A hA (k + a * e) := by
  have hpow : ∀ a : ℕ, q ^ a • Q ∈ formalFilt A hA (k + a * e) := by
    intro a
    induction a with
    | zero => simpa using hQ
    | succ a ih =>
      rw [pow_succ, mul_nsmul]
      have := nsmul_mem_formalFilt_add hA hq he0 he4 ih
      convert this using 2; push_cast; ring
  rw [mul_nsmul]
  exact (formalFilt A hA (k + a * e)).nsmul_mem (hpow a) n

end ZInQ.Size
