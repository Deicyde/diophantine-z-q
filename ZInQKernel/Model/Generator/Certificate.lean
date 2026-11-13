import ZInQKernel.Model.Generator.InfiniteOrder
import ZInQKernel.Model.Descent.RankOne
import ZInQKernel.Model.Descent.OddIndex
import ZInQKernel.Model.Heights.SmallPoints
import ZInQKernel.Model.Heights.Translates
import ZInQKernel.Model.Heights.SearchBox

/-!
# The generator certificate

Blueprint: `model/generator.md` (Proposition 3.1).

`P₀` has infinite order and `2E(K₀) = ℤ P₀`. Work on `C` through `θ`. By rank one,
`C(K₀) = ℤ S ⊕ C(K₀)[2]`; write `R = [m] S + T`, so `m` is odd. If `|m| ≥ 3`, then
`h_x(S) < log 9`, so `x(S)` is one of the seven survivors of the finite search. The survivors
`0, ±δ` are abscissas of two-torsion points, and the other four are the abscissas of `R + T'`,
`T' ∈ C(K₀)[2]`, so `ĥ(S) = ĥ(R)`; but `ĥ(R) = m² ĥ(S)` with `m² ≥ 9` and `ĥ(R) > 0`. Hence
`m = ±1` and `2C(K₀) = ℤ [2]R`, which `θ⁻¹` sends to `ℤ P₀`.

The Mordell–Weil theorem is used through `exists_generator_C'` (it is proved, `mordellWeilE`),
so no hypothesis remains.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Small points of `C` have the canonical height of `R` -/

/-- Points of `C` with equal abscissas are equal or opposite. -/
theorem curveC_eq_or_eq_neg_of_X_eq {x y x' y' : K0} (h : curveC.toAffine.Nonsingular x y)
    (h' : curveC.toAffine.Nonsingular x' y') (hx : x = x') :
    Point.some x y h = .some x' y' h' ∨ Point.some x y h = -Point.some x' y' h' := by
  rcases Y_eq_of_X_eq h.1 h'.1 hx with hy | hy
  · left; simp only [Point.some.injEq]; exact ⟨hx, hy⟩
  · right; rw [Point.neg_some]; simp only [Point.some.injEq]; exact ⟨hx, hy⟩

/-- A point with the abscissa of a translate `R + T'` by two-torsion has the canonical height
of `R`. -/
theorem canonHeight_eq_of_X_eq_translate {x y : K0} (h : curveC.toAffine.Nonsingular x y)
    {T' : curveC.toAffine.Point} (hT' : 2 • T' = 0)
    (hR : ∃ y' h', pointR + T' = Point.some x y' h') :
    canonHeight (.some x y h) = canonHeight pointR := by
  obtain ⟨y', h', hR⟩ := hR
  rcases curveC_eq_or_eq_neg_of_X_eq h h' rfl with e | e
  · rw [e, ← hR, canonHeight_add_twoTorsion _ _ hT']
  · rw [e, canonHeight_neg, ← hR, canonHeight_add_twoTorsion _ _ hT']

/-- An affine point of `C` with abscissa `0`, `δ` or `-δ` is two-torsion. -/
theorem two_nsmul_eq_zero_of_X_two_torsion {x y : K0} (h : curveC.toAffine.Nonsingular x y)
    (hx : x = 0 ∨ x = delta ∨ x = -delta) : 2 • Point.some x y h = 0 := by
  refine (shortCurve_two_nsmul_some_eq_zero_iff (A := -delta ^ 2) h).mpr ?_
  have he := (curveC_equation_iff x y).mp h.1
  have hy : y ^ 2 = 0 := by
    rw [he]; rcases hx with hx | hx | hx <;> rw [hx] <;> ring
  rw [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy]

/-- A nontorsion point `S` of `C` with `h_x(S) < log 9` has the canonical height of `R`. -/
theorem canonHeight_eq_of_hx_lt {S : curveC.toAffine.Point} (hS : ¬ IsOfFinAddOrder S)
    (hx9 : hx S < Real.log 9) : canonHeight S = canonHeight pointR := by
  rcases S with _ | ⟨x, y, h⟩
  · exact absurd (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, one_pos, nsmul_zero 1⟩) hS
  have hx := small_point_abscissa h hx9
  simp only [smallSurvivors, Finset.mem_insert, Finset.mem_singleton] at hx
  have htor : ¬ (x = 0 ∨ x = delta ∨ x = -delta) := fun ht =>
    hS (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, two_pos, two_nsmul_eq_zero_of_X_two_torsion h ht⟩)
  rcases hx with hx | hx | hx | rfl | rfl | rfl | rfl
  · exact absurd (Or.inl hx) htor
  · exact absurd (Or.inr (Or.inl hx)) htor
  · exact absurd (Or.inr (Or.inr hx)) htor
  · exact canonHeight_eq_of_X_eq_translate h (T' := 0) (by simp) ⟨_, _, by rw [add_zero]; rfl⟩
  · exact canonHeight_eq_of_X_eq_translate h ((curveC_two_torsion _).mpr (by simp))
      x_pointR_add_cT0
  · exact canonHeight_eq_of_X_eq_translate h ((curveC_two_torsion _).mpr (by simp))
      x_pointR_add_cTdelta
  · exact canonHeight_eq_of_X_eq_translate h ((curveC_two_torsion _).mpr (by simp))
      x_pointR_add_cTnegdelta

/-! ### The free index of `R` is `±1` -/

/-- If `R = [m] S + T` with `S` of infinite order and `T ∈ C(K₀)[2]`, then `m = ±1`. -/
theorem abs_free_index_eq_one {S T : curveC.toAffine.Point} {m : ℤ} (hS : ¬ IsOfFinAddOrder S)
    (hT : 2 • T = 0) (hR : pointR = m • S + T) : |m| = 1 := by
  have hodd := odd_free_index S T m hT hR
  by_contra h1
  have hm3 : 3 ≤ |m| := by
    obtain ⟨k, rfl⟩ := hodd
    rcases abs_cases (2 * k + 1) with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at h1 ⊢ <;> omega
  have hS9 := (hx_lt_log_nine_of_multiple S T m hR hT hm3).2
  have hSR := canonHeight_eq_of_hx_lt hS hS9
  have hRS : canonHeight pointR = (m : ℝ) ^ 2 * canonHeight S := by
    rw [hR, canonHeight_add_twoTorsion _ _ hT, canonHeight_zsmul]
  have hpos := canonHeight_R_pos.2.2.2
  have hm2 : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm3
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  rw [hSR] at hRS
  nlinarith

/-! ### `2C(K₀) = ℤ [2]R` and `2E(K₀) = ℤ P₀` -/

/-- `2C(K₀) = ℤ [2]R`. -/
theorem two_nsmul_range_C_eq_zmultiples :
    (nsmulAddMonoidHom (α := curveC.toAffine.Point) 2).range =
      AddSubgroup.zmultiples (2 • pointR) := by
  obtain ⟨S, hS, hdec⟩ := exists_generator_C'
  obtain ⟨⟨m, T⟩, hR, -⟩ := hdec pointR
  dsimp only at hR
  have hm : m * m = 1 := by
    have := abs_free_index_eq_one hS T.2 hR
    rcases abs_cases m with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at this
    · rw [this]; rfl
    · rw [show m = -1 by omega]; rfl
  have e : ∀ X : curveC.toAffine.Point, 2 • X = (2 : ℤ) • X := fun X => by
    rw [two_nsmul, two_zsmul]
  -- `[2] S = [2m] R`
  have h2R : (2 : ℤ) • pointR = (2 * m) • S := by
    rw [hR, zsmul_add, ← e T.1, T.2, add_zero, smul_smul]
  have h2S : (2 : ℤ) • S = (2 * m) • pointR := by
    rw [mul_comm, ← smul_smul, h2R, smul_smul]
    congr 1; linear_combination -2 * hm
  ext P
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨Q, rfl⟩
    obtain ⟨⟨n, T'⟩, hQ, -⟩ := hdec Q
    dsimp only at hQ
    refine ⟨n * m, ?_⟩
    rw [hQ, nsmul_add, T'.2, add_zero, e (n • S), e pointR]
    calc (n * m) • (2 : ℤ) • pointR = n • (2 * m) • pointR := by
          rw [smul_smul, smul_smul]; congr 1; ring
      _ = (2 : ℤ) • n • S := by rw [← h2S, smul_smul, smul_smul, mul_comm]
  · rintro ⟨k, rfl⟩
    exact ⟨k • pointR, by rw [e, e, smul_smul, smul_smul, mul_comm]⟩

/-- `P₀ = [2] θ⁻¹(R)`. -/
theorem genP0_eq_two_nsmul : genP0 = 2 • theta.symm pointR := by
  rw [← map_nsmul, theta_symm_two_smul_pointR]

/-- **The generator certificate** (Proposition 3.1): `2E(K₀) = ℤ P₀`. -/
theorem two_smul_range_eq_zmultiples :
    (nsmulAddMonoidHom (α := genCurve.toAffine.Point) 2).range =
      AddSubgroup.zmultiples genP0 := by
  ext P
  have hC := SetLike.ext_iff.mp two_nsmul_range_C_eq_zmultiples (theta P)
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_zmultiples_iff]
    at hC ⊢
  constructor
  · rintro ⟨Q, rfl⟩
    obtain ⟨k, hk⟩ := hC.mp ⟨theta Q, (map_nsmul theta 2 Q).symm⟩
    refine ⟨k, theta.injective ?_⟩
    rw [map_zsmul, theta_genP0, hk, map_nsmul]
  · rintro ⟨k, rfl⟩
    refine ⟨k • theta.symm pointR, ?_⟩
    rw [genP0_eq_two_nsmul, two_nsmul, two_nsmul, zsmul_add]

/-- The carrier `D = 2E(K₀)` is `ℤ P₀`. -/
theorem carrierD_eq_zmultiples : carrierD = AddSubgroup.zmultiples genP0 := by
  rw [← two_smul_range_eq_zmultiples]
  ext P
  rw [mem_carrierD]
  simp [AddMonoidHom.mem_range]

/-- **Proposition 3.1**: `P₀` has infinite order and `2E(K₀) = ℤ P₀`. -/
theorem generator_certificate :
    ¬ IsOfFinAddOrder genP0 ∧ carrierD = AddSubgroup.zmultiples genP0 :=
  ⟨genP0_not_isOfFinAddOrder, carrierD_eq_zmultiples⟩

theorem mem_carrierD_iff_exists_zsmul {P : genCurve.toAffine.Point} :
    P ∈ carrierD ↔ ∃ n : ℤ, n • genP0 = P := by
  rw [carrierD_eq_zmultiples, AddSubgroup.mem_zmultiples_iff]

/-- `n ↦ [n] P₀` is injective. -/
theorem zsmul_genP0_injective : Function.Injective fun n : ℤ => n • genP0 :=
  injective_zsmul_iff_not_isOfFinAddOrder.mpr genP0_not_isOfFinAddOrder

/-- `n ↦ [n] P₀` is an isomorphism `ℤ ≃+ D = 2E(K₀)`. -/
noncomputable def indexEquivCarrier : ℤ ≃+ carrierD :=
  AddEquiv.ofBijective
    ((zmultiplesHom genCurve.toAffine.Point genP0).codRestrict carrierD fun n =>
      mem_carrierD_iff_exists_zsmul.mpr ⟨n, rfl⟩)
    ⟨fun a b h => zsmul_genP0_injective (congrArg Subtype.val h), fun P => by
      obtain ⟨n, hn⟩ := mem_carrierD_iff_exists_zsmul.mp P.2
      exact ⟨n, Subtype.ext hn⟩⟩

@[simp] theorem indexEquivCarrier_apply (n : ℤ) :
    (indexEquivCarrier n : genCurve.toAffine.Point) = n • genP0 := rfl

/-- The carrier `D` is torsion-free. -/
theorem eq_zero_of_mem_carrierD_of_isOfFinAddOrder {P : genCurve.toAffine.Point}
    (hP : P ∈ carrierD) (hfin : IsOfFinAddOrder P) : P = 0 := by
  obtain ⟨n, rfl⟩ := mem_carrierD_iff_exists_zsmul.mp hP
  obtain ⟨k, hk, hkP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin
  have h : ((k : ℤ) * n) • genP0 = (0 : ℤ) • genP0 := by
    rw [mul_zsmul, natCast_zsmul, hkP, zero_zsmul]
  have := zsmul_genP0_injective h
  rcases mul_eq_zero.mp this with h | h
  · omega
  · rw [h, zero_zsmul]

end ZInQ
