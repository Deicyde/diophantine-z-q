import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.WeierstrassParameter
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ProjectiveParameter

/-!
# The invariant differential of a Weierstrass curve in the parameter at infinity

On the function field `L(E)` of a nonsingular Weierstrass curve, with `z = -x/y`, `w = -1/y` and
`u = 1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²`, the valuation at infinity of `u - 1` is below `1`
(`z` and `w` have valuations `exp(-1)` and `exp(-3)`, the constants at most `1`), so
`v_∞(u) = 1` and `u ≠ 0` (`localUnit_genericPoint_ne_zero`). Hence, in `Ω[L(E)/L]`,

`ω = dx/(2y + a₁x + a₃) = u⁻¹ • d(-x/y)`   (`invariantDifferential_eq_localUnit_inv_smul`),

the expansion of the invariant differential at the origin `O` with leading coefficient `1`.

Locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, IV.1.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open KaehlerDifferential
open ZInQ.Contrib.RC53Assist.S2aNumberField
open WeierstrassCurve (Affine.infinityPlace)

variable {L : Type} [Field L] (E : WeierstrassCurve L)

/-- THEOREM (proved). Constants have valuation at most `1` at infinity. Locator:
`algebraMap_mem_stalkPointOImage`, `infinityPlace_le_one_of_mem_stalkPointOImage`. -/
theorem infinityPlace_algebraMap_le_one (c : L) :
    Affine.infinityPlace E.toAffine (algebraMap L E.toAffine.FunctionField c) ≤ 1 :=
  infinityPlace_le_one_of_mem_stalkPointOImage E (algebraMap_mem_stalkPointOImage E c)

/-- THEOREM (proved). A constant times an element of valuation below `1` has valuation below `1`.
Locator: `infinityPlace_algebraMap_le_one`. -/
theorem infinityPlace_const_mul_lt_one (c : L) {t : E.toAffine.FunctionField}
    (ht : Affine.infinityPlace E.toAffine t < 1) :
    Affine.infinityPlace E.toAffine (algebraMap L E.toAffine.FunctionField c * t) < 1 := by
  rw [map_mul, mul_comm]
  exact mul_lt_one_of_lt_of_le ht (infinityPlace_algebraMap_le_one E c)

/-- THEOREM (proved). `v_∞(u - 1) < 1` for the local unit at the generic point. Locator:
`infinityPlace_paramZ`, `infinityPlace_paramW`; Mathlib, `Valuation.map_add_lt`. -/
theorem infinityPlace_localUnit_sub_one_lt :
    Affine.infinityPlace E.toAffine
      (localUnit E (-E.toAffine.genericX / E.toAffine.genericY) (-1 / E.toAffine.genericY) - 1)
      < 1 := by
  set v := Affine.infinityPlace E.toAffine
  set z := -E.toAffine.genericX / E.toAffine.genericY
  set w := -1 / E.toAffine.genericY
  have hz : v z < 1 := by
    rw [infinityPlace_paramZ, WithZero.exp_lt_one_iff]
    norm_num
  have hw : v w < 1 := by
    rw [infinityPlace_paramW, WithZero.exp_lt_one_iff]
    norm_num
  have hzz : v (z ^ 2) < 1 := by
    rw [pow_two, map_mul]
    exact mul_lt_one_of_lt_of_le hz hz.le
  have hzw : v (z * w) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hz hw.le
  have hww : v (w ^ 2) < 1 := by
    rw [pow_two, map_mul]
    exact mul_lt_one_of_lt_of_le hw hw.le
  have heq : localUnit E z w - 1 =
      -(algebraMap L E.toAffine.FunctionField E.a₁ * z) +
        -(algebraMap L E.toAffine.FunctionField E.a₂ * z ^ 2) +
        -(algebraMap L E.toAffine.FunctionField (2 * E.a₃) * w) +
        -(algebraMap L E.toAffine.FunctionField (2 * E.a₄) * (z * w)) +
        -(algebraMap L E.toAffine.FunctionField (3 * E.a₆) * w ^ 2) := by
    simp only [localUnit, map_mul, map_ofNat]
    ring
  rw [heq]
  refine v.map_add_lt (v.map_add_lt (v.map_add_lt (v.map_add_lt ?_ ?_) ?_) ?_) ?_ <;>
    rw [Valuation.map_neg] <;> exact infinityPlace_const_mul_lt_one E _ (by assumption)

/-- THEOREM (proved). The local unit at the generic point is nonzero: its valuation at infinity is
`1`. Locator: `infinityPlace_localUnit_sub_one_lt`; Mathlib, `Valuation.map_one_add_of_lt`. -/
theorem localUnit_genericPoint_ne_zero :
    localUnit E (-E.toAffine.genericX / E.toAffine.genericY) (-1 / E.toAffine.genericY) ≠ 0 := by
  intro h0
  have h1 := (Affine.infinityPlace E.toAffine).map_one_add_of_lt
    (infinityPlace_localUnit_sub_one_lt E)
  rw [add_sub_cancel, h0, map_zero] at h1
  exact zero_ne_one h1

/-- THEOREM (proved). **The invariant differential in the parameter at infinity**:
`dx/(2y + a₁x + a₃) = u⁻¹ • d(-x/y)` in `Ω[L(E)/L]`. Locator: Silverman, IV.1;
`invariant_eq_localUnit_inv_smul`, `localUnit_genericPoint_ne_zero`. -/
theorem invariantDifferential_eq_localUnit_inv_smul [E.IsElliptic] :
    WeierstrassCurve.Affine.invariantDifferential E.toAffine =
      (localUnit E (-E.toAffine.genericX / E.toAffine.genericY) (-1 / E.toAffine.genericY))⁻¹ •
        D L E.toAffine.FunctionField (-E.toAffine.genericX / E.toAffine.genericY) := by
  have hP := WeierstrassCurve.Affine.invariantDifferentialDenom_ne_zero E.toAffine
  rw [WeierstrassCurve.Affine.invariantDifferentialDenom_def] at hP
  rw [WeierstrassCurve.Affine.invariantDifferential_def,
    WeierstrassCurve.Affine.invariantDifferentialDenom_def]
  exact invariant_eq_localUnit_inv_smul E _ _ (genericPoint_equation E) (genericY_ne_zero E) hP
    (localUnit_genericPoint_ne_zero E)

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
