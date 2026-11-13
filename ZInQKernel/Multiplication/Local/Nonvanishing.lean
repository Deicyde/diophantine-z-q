import ZInQKernel.Multiplication.Local.Dyadic
import ZInQKernel.Multiplication.Local.TruncationUnit
import ZInQKernel.Model.Generator.InfiniteOrder

/-!
# The truncated logarithm does not vanish on nonzero multiples of `P₀`

Blueprint: `multiplication/local/logarithm-nonvanishing.md`.

For `n ≠ 0`, `Q = [n]P₀` is affine with `x(Q) ≠ 0`, `y(Q) ≠ 0`, and `L(z(Q)) ≠ 0`: `Q ≠ O`
because `P₀` has infinite order, `Q` lies in the dyadic formal group with `v_s(z(Q)) ≥ 3`,
and `L(z) = 16575 z (1 + η)` there.

The article assumes the Mordell–Weil hypothesis for "`P₀` has infinite order". This follows
unconditionally from the torsion theorem of `Model/Descent` (`E(K₀)_tors = E(K₀)[2]`,
`two_nsmul_eq_zero_of_isOfFinAddOrder`), so the statement below has no hypothesis.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

theorem zsmul_genP0_ne_zero {n : ℤ} (hn : n ≠ 0) : n • genP0 ≠ 0 := by
  intro h
  exact genP0_not_isOfFinAddOrder (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n, hn, h⟩)

/-- **The truncated logarithm does not vanish on nonzero multiples of `P₀`.** For `n ≠ 0`,
`[n]P₀ = (x, y)` is affine with `x ≠ 0`, `y ≠ 0`, and `L(-x/y) ≠ 0`. -/
theorem log25_z_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∃ x y h, n • genP0 = Point.some x y h ∧ x ≠ 0 ∧ y ≠ 0 ∧
      truncLog (genD ^ 2) (-x / y) ≠ 0 := by
  obtain ⟨hW1, hz⟩ := zsmul_genP0_mem_formal n
  have hne := zsmul_genP0_ne_zero hn
  generalize hQ : n • genP0 = Q at hW1 hz hne
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hne
  obtain ⟨N, hN, -, -, hy0, -⟩ := formal_val_x_y vS_genA_nonneg h hW1
  have hx0 : x ≠ 0 := by
    intro h0; have hx : vS x < 0 := hW1; rw [h0, vS.map_zero] at hx; exact not_top_lt hx
  refine ⟨x, y, h, rfl, hx0, hy0, ?_⟩
  refine log25_ne_zero prime_sqrt2Z (div_ne_zero (neg_ne_zero.mpr hx0) hy0) ?_
  exact le_trans (show ((1 : ℤ) : WithTop ℤ) ≤ ((3 : ℤ) : WithTop ℤ) from
    WithTop.coe_le_coe.mpr (by norm_num)) hz

end ZInQ.Mult
