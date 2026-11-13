import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.Package
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.PropN WeierstrassCurve.Affine

theorem nonsingular_00 : curveAbar.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  refine ⟨by norm_num, Or.inl ?_⟩
  norm_num

/-- `τ(1) = (0, 0)`. -/
def pt00 : PtA := .some 0 0 nonsingular_00

theorem ptT_add_self : ptT + ptT = pt00 := by
  have hy : (-4 : Qbar) ≠ curveAbar.toAffine.negY 2 (-4) := by
    simp only [negY, curveAbar_a₁, curveAbar_a₃]; norm_num
  rw [ptT, Point.add_self_of_Y_ne hy, pt00, Point.some.injEq]
  have hs : curveAbar.toAffine.slope 2 2 (-4) (-4) = -2 := by
    rw [slope_of_Y_ne rfl hy]
    simp only [negY, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄]; norm_num
  simp only [addX, addY, negAddY, negY, hs, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor <;> norm_num

theorem pt00_add_self : pt00 + pt00 = 0 := by
  rw [pt00]
  exact Point.add_self_of_Y_eq (by simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring)

theorem iPt_pt00 : iPt pt00 = pt00 := by
  rw [pt00, iPt_some, Point.some.injEq]; constructor <;> ring

theorem two_zsmul_ptT : (2 : ℤ) • ptT = pt00 := by rw [two_zsmul, ptT_add_self]

theorem four_zsmul_ptT : (4 : ℤ) • ptT = 0 := by
  rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_zsmul, two_zsmul_ptT, two_zsmul, pt00_add_self]

theorem two_zsmul_iPt_ptT : (2 : ℤ) • iPt ptT = pt00 := by
  rw [← iPt_zsmul, two_zsmul_ptT, iPt_pt00]

theorem zsmul_ptT_emod (k : ℤ) : k • ptT = (k % 4) • ptT := by
  rw [show k • ptT = (k % 4 + 4 * (k / 4)) • ptT by congr 1; omega]
  rw [add_zsmul, mul_comm, mul_zsmul, four_zsmul_ptT, zsmul_zero, add_zero]

theorem nonsingular_T' : curveAbar.toAffine.Nonsingular 2 4 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  refine ⟨by norm_num, Or.inr ?_⟩
  norm_num

theorem neg_ptT : -ptT = .some 2 4 nonsingular_T' := by
  rw [ptT, Point.neg_some, Point.some.injEq]
  simp only [negY, curveAbar_a₁, curveAbar_a₃]; norm_num

/-- The four multiples of `T`. -/
theorem zsmul_ptT_cases (k : ℤ) :
    k • ptT = 0 ∧ k % 4 = 0 ∨ k • ptT = ptT ∧ k % 4 = 1 ∨ k • ptT = pt00 ∧ k % 4 = 2 ∨
      k • ptT = -ptT ∧ k % 4 = 3 := by
  rw [zsmul_ptT_emod]
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % 4
  · simp
  · simp
  · simp [two_zsmul_ptT]
  · right; right; right
    refine ⟨?_, rfl⟩
    rw [show (3 : ℤ) = 4 + -1 by norm_num, add_zsmul, four_zsmul_ptT, neg_one_zsmul, zero_add]


theorem iPt_ptT_ne (k : ℤ) : iPt ptT ≠ k • ptT := by
  rcases zsmul_ptT_cases k with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rw [ptT, iPt_some]; exact Point.some_ne_zero _
  · rw [ptT, iPt_some, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this
  · rw [ptT, iPt_some, pt00, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this
  · rw [neg_ptT, ptT, iPt_some, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this

theorem tauG_mk (a b : ℤ) : tauG ⟨a, b⟩ = a • ptT + b • iPt ptT := rfl

theorem twoTwoI_dvd_iff (a b : ℤ) : twoTwoI ∣ (⟨a, b⟩ : GaussianInt) ↔ 2 ∣ b ∧ 4 ∣ a + b := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 := congrArg Zsqrtd.re hw
    have h2 := congrArg Zsqrtd.im hw
    simp only [twoTwoI, Zsqrtd.re_mul, Zsqrtd.im_mul] at h1 h2
    exact ⟨⟨w.re + w.im, by linarith⟩, ⟨w.re, by linarith⟩⟩
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    refine ⟨⟨r, q - r⟩, ?_⟩
    ext <;> simp only [twoTwoI, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> linarith

/-- **TYZ L1386 for the pinned `τ`**: `τ(y/2) = 0 ↔ y ∈ (2 + 2i)ℤ[i]`. -/
theorem tauG_eq_zero (y : GaussianInt) : tauG y = 0 ↔ twoTwoI ∣ y := by
  obtain ⟨a, b⟩ := y
  rw [twoTwoI_dvd_iff, tauG_mk]
  have hb : b • iPt ptT = (b % 2) • iPt ptT + (b / 2) • pt00 := by
    rw [show b • iPt ptT = (b % 2 + 2 * (b / 2)) • iPt ptT by congr 1; omega]
    rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul_iPt_ptT]
  have hT : a • ptT + (b / 2) • pt00 = (a + 2 * (b / 2)) • ptT := by
    rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul_ptT]
  have hb2 : b % 2 = 0 ∨ b % 2 = 1 := Int.emod_two_eq_zero_or_one b
  rcases hb2 with h | h
  · rw [hb, h, zero_zsmul, zero_add, hT]
    have hbe : b = 2 * (b / 2) := by omega
    rcases zsmul_ptT_cases (a + 2 * (b / 2)) with ⟨e, hm⟩ | ⟨e, hm⟩ | ⟨e, hm⟩ | ⟨e, hm⟩ <;>
      rw [e]
    · exact ⟨fun _ => ⟨⟨b / 2, by omega⟩, by omega⟩, fun _ => rfl⟩
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [ptT] at h0; exact absurd h0 (Point.some_ne_zero _)
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [pt00] at h0; exact absurd h0 (Point.some_ne_zero _)
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [neg_ptT] at h0; exact absurd h0 (Point.some_ne_zero _)
  · rw [hb, h, one_zsmul]
    refine ⟨fun h0 => ?_, fun h0 => by omega⟩
    exfalso
    have h1 : iPt ptT = (-(a + 2 * (b / 2))) • ptT := by
      rw [neg_zsmul, ← hT, eq_neg_iff_add_eq_zero, ← h0]; abel
    exact iPt_ptT_ne _ h1

end ZInQ.Contrib.TYZGenus.Package
