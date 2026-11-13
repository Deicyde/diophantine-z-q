import ZInQKernel.Model.Generator.Certificate
import ZInQKernel.Model.Generator.GroupLaw
import ZInQKernel.Syntax.Templates.Member

/-!
# Polynomial membership in the doubled group

Blueprint: `model/membership.md`, `model/membership-indices.md`.

`Rel_member(p)` (the membership template `memberTemplate` vanishes at `p` and some rational values
of its seven witnesses) holds exactly when `p` is the code of a point of `2E(K₀)`. The template
polynomial is `κ(φ_member)²`, so it vanishes exactly when a branch of `φ_member` holds
(`memberTemplate_rel_iff`); pair arithmetic turns the doubling branch into equations in `K₀`
(`memberTemplate_rel_iff_spec`), and the doubling branch describes `[2](X, Y)` with `Y ≠ 0`.
With the generator certificate, accepted inputs are exactly the codes `ι(n)`, each with a unique
index.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Syntax

/-! ### Formulas in field terms -/

theorem Syntax.ev_norm_eq (x : ℕ → ℚ) (u : Pair) :
    ev x u.norm = QuadraticAlgebra.norm (Pair.val x u) := by
  rw [Pair.ev_norm, K0.norm_eq]; rfl

theorem K0.C_two : (QuadraticAlgebra.C (2 : ℚ) : K0) = 2 := QuadraticAlgebra.C_ofNat 2

theorem K0.C_three : (QuadraticAlgebra.C (3 : ℚ) : K0) = 3 := QuadraticAlgebra.C_ofNat 3

/-- `φ_member` in field terms, at any assignment. -/
theorem holds_memberFormula (x : ℕ → ℚ) (p : Code) (X Y H : Pair) (u : ℕ) :
    (memberFormula p X Y H u).Holds x ↔ evCode x p = ![1, 0, 0, 0, 0] ∨
      (ev x (p 0) = 0 ∧ Pair.val x Y ^ 2 = Pair.val x X ^ 3 + -genD ^ 2 * Pair.val x X ∧
        QuadraticAlgebra.norm (Pair.val x Y) * x u = 1 ∧
        2 * Pair.val x Y * Pair.val x H = 3 * Pair.val x X ^ 2 + -genD ^ 2 ∧
        Pair.val x p.x = Pair.val x H ^ 2 - 2 * Pair.val x X ∧
        Pair.val x p.y =
          Pair.val x H * (Pair.val x X - (Pair.val x H ^ 2 - 2 * Pair.val x X)) - Pair.val x Y) := by
  simp only [memberFormula, Formula.holds_or, Formula.holds_and, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, holds_feq, holds_isO,
    holds_fin, holds_curve, holds_nzFormula, ev_norm_eq, Pair.val_sub, Pair.val_smul, Pair.val_sq,
    Pair.val_mul, Pair.val_add, Pair.val_A, ev_ofNat, K0.C_two, K0.C_three]

/-- The membership branch formula in field terms: `p` is `O`, or for some `X, Y, H ∈ K₀` and
`u ∈ ℚ`: `p₀ = 0`, `Y² = X³ - d² X`, `u N(Y) = 1`, `2 Y H = 3 X² - d²`, `x = H² - 2X` and
`y = H (X - (H² - 2X)) - Y`, where `x = p₁ + p₂ s`, `y = p₃ + p₄ s`. -/
def MemberSpec (p : Fin 5 → ℚ) : Prop :=
  p = ![1, 0, 0, 0, 0] ∨ ∃ X Y H : K0, ∃ u : ℚ, p 0 = 0 ∧ Y ^ 2 = X ^ 3 - genD ^ 2 * X ∧
    u * QuadraticAlgebra.norm Y = 1 ∧ 2 * Y * H = 3 * X ^ 2 - genD ^ 2 ∧
    codeX p = H ^ 2 - 2 * X ∧ codeY p = H * (X - (H ^ 2 - 2 * X)) - Y

section Assign

variable (a : Fin 5 → ℚ) (y : Fin 7 → ℚ)

theorem evCode_assign_member : evCode (assign 5 7 a y) (varPoint 0) = a := by
  funext i
  simp only [evCode, ev_varPoint, zero_add]
  exact assign_of_lt a y i.isLt

theorem val_assign_member_x : Pair.val (assign 5 7 a y) (varPoint 0).x = codeX a := by
  ext
  · simp only [Pair.re_val, Code.x, varPoint, ev_X]; exact assign_of_lt (i := 1) a y (by omega)
  · simp only [Pair.im_val, Code.x, varPoint, ev_X]; exact assign_of_lt (i := 2) a y (by omega)

theorem val_assign_member_y : Pair.val (assign 5 7 a y) (varPoint 0).y = codeY a := by
  ext
  · simp only [Pair.re_val, Code.y, varPoint, ev_X]; exact assign_of_lt (i := 3) a y (by omega)
  · simp only [Pair.im_val, Code.y, varPoint, ev_X]; exact assign_of_lt (i := 4) a y (by omega)

theorem val_assign_member_X : Pair.val (assign 5 7 a y) (varPair 5) = ⟨y 0, y 1⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_add 5 7 a y 0
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_add 5 7 a y 1

theorem val_assign_member_Y : Pair.val (assign 5 7 a y) (varPair 7) = ⟨y 2, y 3⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_add 5 7 a y 2
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_add 5 7 a y 3

theorem val_assign_member_H : Pair.val (assign 5 7 a y) (varPair 9) = ⟨y 4, y 5⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_add 5 7 a y 4
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_add 5 7 a y 5

end Assign

/-- **The membership template in field terms**: `Rel_member(p) ↔ MemberSpec p`. -/
theorem memberTemplate_rel_iff_spec (p : Fin 5 → ℚ) : memberTemplate.Rel p ↔ MemberSpec p := by
  rw [memberTemplate_rel_iff]
  simp only [holds_memberFormula, evCode_assign_member, val_assign_member_x, val_assign_member_y,
    val_assign_member_X, val_assign_member_Y, val_assign_member_H]
  have h0 : ∀ y : Fin 7 → ℚ, ev (assign 5 7 p y) (varPoint 0 0) = p 0 := fun y =>
    congrFun (evCode_assign_member p y) 0
  have h11 : ∀ y : Fin 7 → ℚ, assign 5 7 p y 11 = y 6 := fun y => assign_add 5 7 p y 6
  simp only [h0, h11, MemberSpec, exists_or, exists_const]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, h0, hc, hu, hH, hx, hy⟩
    exact ⟨_, _, _, y 6, h0, by rw [hc]; ring, by rw [mul_comm]; exact hu, by rw [hH]; ring,
      hx, hy⟩
  · rintro ⟨X, Y, H, u, h0, hc, hu, hH, hx, hy⟩
    let v : Fin 7 → ℚ := ![X.re, X.im, Y.re, Y.im, H.re, H.im, u]
    have eX : (⟨v 0, v 1⟩ : K0) = X := rfl
    have eY : (⟨v 2, v 3⟩ : K0) = Y := rfl
    have eH : (⟨v 4, v 5⟩ : K0) = H := rfl
    have e6 : v 6 = u := rfl
    refine ⟨v, h0, ?_⟩
    rw [eX, eY, eH, e6]
    exact ⟨by rw [hc]; ring, by rw [mul_comm]; exact hu, by rw [hH]; ring, hx, hy⟩

/-! ### Points of `2E(K₀)` -/

/-- **Polynomial membership, field form**: `MemberSpec p` holds exactly when `p` is the code of
a point of `2E(K₀)`. -/
theorem memberSpec_iff (p : Fin 5 → ℚ) :
    MemberSpec p ↔
      ∃ Q ∈ (nsmulAddMonoidHom (α := genCurve.toAffine.Point) 2).range, p = pointCode Q := by
  constructor
  · rintro (rfl | ⟨X, Y, H, u, h0, hc, hu, hH, hx, hy⟩)
    · exact ⟨0, ⟨0, nsmul_zero 2⟩, rfl⟩
    have hY : Y ≠ 0 := by
      rintro rfl
      rw [K0.norm_eq] at hu
      simp at hu
    have hns : genCurve.toAffine.Nonsingular X Y :=
      equation_iff_nonsingular.mp ((genCurve_equation_iff X Y).mpr hc)
    obtain ⟨h', e⟩ := genCurve_two_nsmul_of_Y_ne hns hY H hH
    refine ⟨2 • Point.some X Y hns, ⟨_, rfl⟩, ?_⟩
    rw [e, eq_pointCode_some_iff]
    exact ⟨h0, by rw [hx]; ring, by rw [hy]; ring⟩
  · rintro ⟨Q, ⟨T, rfl⟩, rfl⟩
    rw [nsmulAddMonoidHom_apply]
    rcases T with _ | ⟨X, Y, h⟩
    · left; rw [show (Point.zero : genCurve.toAffine.Point) = 0 from rfl, nsmul_zero]; rfl
    by_cases hY : Y = 0
    · left; rw [genCurve_two_nsmul_of_Y_eq_zero h hY]; rfl
    right
    have h2Y : (2 : K0) * Y ≠ 0 := mul_ne_zero two_ne_zero hY
    set H := (3 * X ^ 2 - genD ^ 2) / (2 * Y) with hHdef
    have hH : 2 * Y * H = 3 * X ^ 2 - genD ^ 2 := by rw [hHdef]; field_simp
    obtain ⟨h', e⟩ := genCurve_two_nsmul_of_Y_ne h hY H hH
    rw [e]
    have hN : QuadraticAlgebra.norm Y ≠ 0 := fun h0 => hY (K0.norm_eq_zero_iff.mp h0)
    refine ⟨X, Y, H, (QuadraticAlgebra.norm Y)⁻¹, rfl, (genCurve_equation_iff X Y).mp h.1,
      inv_mul_cancel₀ hN, hH, ?_, ?_⟩
    · rw [codeX_pointCode_some]; ring
    · rw [codeY_pointCode_some]; ring

/-- **Polynomial membership in the doubled group** (`model/membership.md`): for every
`p ∈ ℚ⁵`, `Rel_member(p)` holds exactly when `p = code(Q)` for some `Q ∈ 2E(K₀)`. -/
theorem rel_member_iff (p : Fin 5 → ℚ) :
    memberTemplate.Rel p ↔
      ∃ Q ∈ (nsmulAddMonoidHom (α := genCurve.toAffine.Point) 2).range, p = pointCode Q := by
  rw [memberTemplate_rel_iff_spec, memberSpec_iff]

/-- The same with the carrier `D = 2E(K₀)`. -/
theorem rel_member_iff_isCarrierCode (p : Fin 5 → ℚ) :
    memberTemplate.Rel p ↔ IsCarrierCode p := by
  rw [rel_member_iff, IsCarrierCode, carrierD_eq_zmultiples, ← two_smul_range_eq_zmultiples]
  exact ⟨fun ⟨Q, hQ, e⟩ => ⟨Q, hQ, e.symm⟩, fun ⟨Q, hQ, e⟩ => ⟨Q, hQ, e.symm⟩⟩

/-! ### Accepted inputs have unique indices -/

/-- **Accepted inputs are the codes `ι(n)`** (`model/membership-indices.md`). -/
theorem rel_member_iff_iota (p : Fin 5 → ℚ) : memberTemplate.Rel p ↔ ∃ n : ℤ, p = iota n := by
  rw [rel_member_iff, two_smul_range_eq_zmultiples]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n • genP0, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩, rfl⟩

/-- **Accepted inputs have unique indices** (`model/membership-indices.md`): for every `p ∈ ℚ⁵`,
`Rel_member(p)` holds exactly when `p = ι(n)` for a unique `n ∈ ℤ`. -/
theorem rel_member_iff_existsUnique_iota (p : Fin 5 → ℚ) :
    memberTemplate.Rel p ↔ ∃! n : ℤ, p = iota n := by
  rw [rel_member_iff_iota]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn, fun m hm => iota_injective (hm.symm.trans hn)⟩,
    fun h => h.exists⟩

end ZInQ
