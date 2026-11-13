import ZInQKernel.Model.Generator.Membership

/-!
# Raw addition

Blueprint: `model/raw-addition-points.md`, `model/raw-addition.md`.

`Rel_raw_add(p, q, r)` (the raw addition template `rawAddTemplate` vanishes at `(p, q, r) ∈ ℚ¹⁵`
and some rational values of its six witnesses) has five branches: (1) `p = O`, `q = r`;
(2) `p₀ = 0`, `q = O`, `p = r`; (3) opposite points and `r = O`; (4) distinct abscissas with the
chord slope `m_g`; (5) doubling with nonzero ordinate and the tangent slope `m_d`. On codes of
points `P, Q ∈ E(K₀)` it holds exactly when `r = code(P + Q)`; on `ι(a), ι(b)` exactly when
`r = ι(a + b)`.

The fifteen parameters are `Fin.append (Fin.append p q) r`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Syntax

/-! ### The formula in field terms -/

theorem Syntax.val_code_x (x : ℕ → ℚ) (p : Code) : Pair.val x p.x = codeX (evCode x p) := rfl

theorem Syntax.val_code_y (x : ℕ → ℚ) (p : Code) : Pair.val x p.y = codeY (evCode x p) := rfl

theorem Syntax.ev_code_zero (x : ℕ → ℚ) (p : Code) : ev x (p 0) = evCode x p 0 := rfl

/-- The raw addition branch formula in field terms, with `x, y` the coordinates encoded by `p`,
`x', y'` those of `q`, `x_r, y_r` those of `r` and `O = (1, 0, 0, 0, 0)`:
(1) `p = O ∧ q = r`; (2) `p₀ = 0 ∧ q = O ∧ p = r`; (3) `p₀ = q₀ = 0`, `x = x'`, `y = -y'`, `r = O`;
(4) `p₀ = q₀ = 0` and for some `m_g ∈ K₀`, `u_g ∈ ℚ`: `u_g N(x' - x) = 1`, `(x' - x) m_g = y' - y`,
`r₀ = 0`, `x_r = m_g² - x - x'`, `y_r = m_g (x - (m_g² - x - x')) - y`;
(5) `p₀ = q₀ = 0`, `x = x'`, `y = y'` and for some `m_d ∈ K₀`, `u_d ∈ ℚ`: `u_d N(y) = 1`,
`2 y m_d = 3 x² - d²`, `r₀ = 0`, `x_r = m_d² - x - x'`, `y_r = m_d (x - (m_d² - x - x')) - y`. -/
def RawAddSpec (p q r : Fin 5 → ℚ) : Prop :=
  (p = ![1, 0, 0, 0, 0] ∧ q = r) ∨
  (p 0 = 0 ∧ q = ![1, 0, 0, 0, 0] ∧ p = r) ∨
  (p 0 = 0 ∧ q 0 = 0 ∧ codeX p = codeX q ∧ codeY p = -codeY q ∧ r = ![1, 0, 0, 0, 0]) ∨
  (p 0 = 0 ∧ q 0 = 0 ∧ ∃ m : K0, ∃ u : ℚ, u * QuadraticAlgebra.norm (codeX q - codeX p) = 1 ∧
    (codeX q - codeX p) * m = codeY q - codeY p ∧ r 0 = 0 ∧
    codeX r = m ^ 2 - codeX p - codeX q ∧
    codeY r = m * (codeX p - (m ^ 2 - codeX p - codeX q)) - codeY p) ∨
  (p 0 = 0 ∧ q 0 = 0 ∧ codeX p = codeX q ∧ codeY p = codeY q ∧ ∃ m : K0, ∃ u : ℚ,
    u * QuadraticAlgebra.norm (codeY p) = 1 ∧ 2 * codeY p * m = 3 * codeX p ^ 2 - genD ^ 2 ∧
    r 0 = 0 ∧ codeX r = m ^ 2 - codeX p - codeX q ∧
    codeY r = m * (codeX p - (m ^ 2 - codeX p - codeX q)) - codeY p)

/-- `φ_add` in field terms, at any assignment. -/
theorem holds_rawAddFormula (x : ℕ → ℚ) (p q r : Code) (mg md : Pair) (ug ud : ℕ) :
    (rawAddFormula p q r mg md ug ud).Holds x ↔
      (evCode x p = ![1, 0, 0, 0, 0] ∧ evCode x q = evCode x r) ∨
      (evCode x p 0 = 0 ∧ evCode x q = ![1, 0, 0, 0, 0] ∧ evCode x p = evCode x r) ∨
      (evCode x p 0 = 0 ∧ evCode x q 0 = 0 ∧ codeX (evCode x p) = codeX (evCode x q) ∧
        codeY (evCode x p) = -codeY (evCode x q) ∧ evCode x r = ![1, 0, 0, 0, 0]) ∨
      (evCode x p 0 = 0 ∧ evCode x q 0 = 0 ∧
        QuadraticAlgebra.norm (codeX (evCode x q) - codeX (evCode x p)) * x ug = 1 ∧
        (codeX (evCode x q) - codeX (evCode x p)) * Pair.val x mg =
          codeY (evCode x q) - codeY (evCode x p) ∧ evCode x r 0 = 0 ∧
        codeX (evCode x r) = Pair.val x mg ^ 2 - codeX (evCode x p) - codeX (evCode x q) ∧
        codeY (evCode x r) = Pair.val x mg * (codeX (evCode x p) -
          (Pair.val x mg ^ 2 - codeX (evCode x p) - codeX (evCode x q))) - codeY (evCode x p)) ∨
      (evCode x p 0 = 0 ∧ evCode x q 0 = 0 ∧ codeX (evCode x p) = codeX (evCode x q) ∧
        codeY (evCode x p) = codeY (evCode x q) ∧
        QuadraticAlgebra.norm (codeY (evCode x p)) * x ud = 1 ∧
        2 * codeY (evCode x p) * Pair.val x md = 3 * codeX (evCode x p) ^ 2 + -genD ^ 2 ∧
        evCode x r 0 = 0 ∧
        codeX (evCode x r) = Pair.val x md ^ 2 - codeX (evCode x p) - codeX (evCode x q) ∧
        codeY (evCode x r) = Pair.val x md * (codeX (evCode x p) -
          (Pair.val x md ^ 2 - codeX (evCode x p) - codeX (evCode x q))) - codeY (evCode x p)) := by
  simp only [rawAddFormula, addOut, Formula.holds_or, Formula.holds_and, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq,
    holds_feq, holds_isO, holds_peq, holds_fin, holds_nzFormula, ev_norm_eq, Pair.val_sub,
    Pair.val_smul, Pair.val_sq, Pair.val_mul, Pair.val_add, Pair.val_neg, Pair.val_A, ev_ofNat,
    K0.C_two, K0.C_three, val_code_x, val_code_y, ev_code_zero, and_assoc]

section Assign

variable (p q r : Fin 5 → ℚ) (y : Fin 6 → ℚ)

theorem evCode_assign_rawAdd_p :
    evCode (assign 15 6 (Fin.append (Fin.append p q) r) y) (varPoint 0) = p := by
  funext i
  simp only [evCode, ev_varPoint, zero_add]
  rw [assign_of_lt _ y (by omega)]
  exact (Fin.append_left (Fin.append p q) r (Fin.castAdd 5 i)).trans (Fin.append_left p q i)

theorem evCode_assign_rawAdd_q :
    evCode (assign 15 6 (Fin.append (Fin.append p q) r) y) (varPoint 5) = q := by
  funext i
  simp only [evCode, ev_varPoint]
  rw [assign_of_lt _ y (by omega)]
  exact (Fin.append_left (Fin.append p q) r (Fin.natAdd 5 i)).trans (Fin.append_right p q i)

theorem evCode_assign_rawAdd_r :
    evCode (assign 15 6 (Fin.append (Fin.append p q) r) y) (varPoint 10) = r := by
  funext i
  simp only [evCode, ev_varPoint]
  rw [assign_of_lt _ y (by omega)]
  exact Fin.append_right (Fin.append p q) r i

theorem val_assign_rawAdd_mg :
    Pair.val (assign 15 6 (Fin.append (Fin.append p q) r) y) (varPair 15) = ⟨y 0, y 1⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_add 15 6 _ y 0
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_add 15 6 _ y 1

theorem val_assign_rawAdd_md :
    Pair.val (assign 15 6 (Fin.append (Fin.append p q) r) y) (varPair 17) = ⟨y 2, y 3⟩ := by
  ext
  · simp only [Pair.re_val, ev_varPair_fst]; exact assign_add 15 6 _ y 2
  · simp only [Pair.im_val, ev_varPair_snd]; exact assign_add 15 6 _ y 3

theorem assign_rawAdd_ug : assign 15 6 (Fin.append (Fin.append p q) r) y 19 = y 4 :=
  assign_add 15 6 _ y 4

theorem assign_rawAdd_ud : assign 15 6 (Fin.append (Fin.append p q) r) y 20 = y 5 :=
  assign_add 15 6 _ y 5

end Assign

/-- **The raw addition template in field terms**: `Rel_raw_add(p, q, r) ↔ RawAddSpec p q r`. -/
theorem rawAddTemplate_rel_iff_spec (p q r : Fin 5 → ℚ) :
    rawAddTemplate.Rel (Fin.append (Fin.append p q) r) ↔ RawAddSpec p q r := by
  rw [rawAddTemplate_rel_iff]
  simp only [holds_rawAddFormula, evCode_assign_rawAdd_p, evCode_assign_rawAdd_q,
    evCode_assign_rawAdd_r, val_assign_rawAdd_mg, val_assign_rawAdd_md, assign_rawAdd_ug,
    assign_rawAdd_ud]
  unfold RawAddSpec
  constructor
  · rintro ⟨y, h | h | h | ⟨h0, h0', hu, hm, hr0, hrx, hry⟩ | ⟨h0, h0', hx, hy, hu, hm, hr0, hrx, hry⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h0', _, y 4, by rw [mul_comm]; exact hu, hm, hr0,
        hrx, hry⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h0', hx, hy, _, y 5, by rw [mul_comm]; exact hu,
        by rw [hm]; ring, hr0, hrx, hry⟩)))
  · rintro (h | h | h | ⟨h0, h0', m, u, hu, hm, hr0, hrx, hry⟩ |
      ⟨h0, h0', hx, hy, m, u, hu, hm, hr0, hrx, hry⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr (Or.inl h)⟩
    · exact ⟨0, Or.inr (Or.inr (Or.inl h))⟩
    · let v : Fin 6 → ℚ := ![m.re, m.im, 0, 0, u, 0]
      have em : (⟨v 0, v 1⟩ : K0) = m := rfl
      have e4 : v 4 = u := rfl
      refine ⟨v, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      rw [em, e4]
      exact ⟨h0, h0', by rw [mul_comm]; exact hu, hm, hr0, hrx, hry⟩
    · let v : Fin 6 → ℚ := ![0, 0, m.re, m.im, 0, u]
      have em : (⟨v 2, v 3⟩ : K0) = m := rfl
      have e5 : v 5 = u := rfl
      refine ⟨v, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
      rw [em, e5]
      exact ⟨h0, h0', hx, hy, by rw [mul_comm]; exact hu, by rw [hm]; ring, hr0, hrx, hry⟩

/-! ### Raw addition on codes of points -/

theorem pointCode_zero' : pointCode (Point.zero : genCurve.toAffine.Point) = ![1, 0, 0, 0, 0] :=
  rfl

theorem pointCode_some_ne_O {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    pointCode (.some x y h) ≠ ![1, 0, 0, 0, 0] :=
  ne_pointCode_zero_of_apply_zero rfl

theorem norm_sub_self_mul_ne_one (z : K0) (u : ℚ) : u * QuadraticAlgebra.norm (z - z) ≠ 1 := by
  rw [sub_self, QuadraticAlgebra.norm_zero, mul_zero]; exact zero_ne_one

/-- **Raw addition on canonical codes, field form**: for `P, Q ∈ E(K₀)`,
`RawAddSpec (code P) (code Q) r ↔ r = code(P + Q)`. -/
theorem rawAddSpec_pointCode_iff (P Q : genCurve.toAffine.Point) (r : Fin 5 → ℚ) :
    RawAddSpec (pointCode P) (pointCode Q) r ↔ r = pointCode (P + Q) := by
  have hO0 : (![1, 0, 0, 0, 0] : Fin 5 → ℚ) 0 ≠ 0 := one_ne_zero
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · -- `P = O`: only branch 1 applies
    rw [pointCode_zero', show (Point.zero : genCurve.toAffine.Point) = 0 from rfl, zero_add]
    simp only [RawAddSpec, hO0, false_and, or_false, true_and]
    exact eq_comm
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · -- `P` affine, `Q = O`: only branch 2 applies
    rw [pointCode_zero', show (Point.zero : genCurve.toAffine.Point) = 0 from rfl, add_zero]
    simp only [RawAddSpec, pointCode_some_ne_O, hO0, pointCode_some_zero, false_and, false_or,
      and_false, or_false, true_and]
    exact eq_comm
  -- both affine: branches 1 and 2 fail
  simp only [RawAddSpec, pointCode_some_ne_O, pointCode_some_zero, codeX_pointCode_some,
    codeY_pointCode_some, false_and, false_or, true_and]
  by_cases hx : x₁ = x₂
  · subst hx
    simp only [true_and]
    by_cases hyy : y₁ = -y₂
    · -- opposite points: branch 3
      have e : Point.some x₁ y₁ h₁ + Point.some x₁ y₂ h₂ = 0 :=
        Point.add_of_Y_eq rfl (by rw [genCurve_negY]; exact hyy)
      rw [e]
      refine ⟨?_, fun hr => Or.inl ⟨hyy, hr⟩⟩
      rintro (⟨-, hr⟩ | ⟨m, u, hu, -⟩ | ⟨rfl, m, u, hu, -⟩)
      · exact hr
      · exact absurd hu (norm_sub_self_mul_ne_one _ _)
      · have : y₁ = 0 := by linear_combination hyy / 2
        rw [this, QuadraticAlgebra.norm_zero, mul_zero] at hu
        exact absurd hu zero_ne_one
    · -- doubling: branch 5
      have hy : y₁ = y₂ := by
        rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with h | h
        · exact h
        · rw [genCurve_negY] at h; exact absurd h hyy
      subst hy
      simp only [true_and]
      have hy0 : y₁ ≠ 0 := by rintro rfl; exact hyy (neg_zero).symm
      have e2 : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₂ = 2 • Point.some x₁ y₁ h₁ := by
        rw [two_nsmul]
      rw [e2]
      constructor
      · rintro (⟨h, -⟩ | ⟨m, u, hu, -⟩ | ⟨m, u, hu, hm, hr0, hrx, hry⟩)
        · exact absurd h hyy
        · exact absurd hu (norm_sub_self_mul_ne_one _ _)
        · obtain ⟨h', e⟩ := genCurve_two_nsmul_of_Y_ne h₁ hy0 m hm
          rw [e, eq_pointCode_some_iff]
          exact ⟨hr0, hrx, hry⟩
      · intro hr
        set m := (3 * x₁ ^ 2 - genD ^ 2) / (2 * y₁) with hmdef
        have hm : 2 * y₁ * m = 3 * x₁ ^ 2 - genD ^ 2 := by
          rw [hmdef]; field_simp
        obtain ⟨h', e⟩ := genCurve_two_nsmul_of_Y_ne h₁ hy0 m hm
        rw [e, eq_pointCode_some_iff] at hr
        have hN : QuadraticAlgebra.norm y₁ ≠ 0 := fun h0 => hy0 (K0.norm_eq_zero_iff.mp h0)
        exact Or.inr (Or.inr ⟨m, _, inv_mul_cancel₀ hN, hm, hr⟩)
  · -- distinct abscissas: branch 4
    have hx' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    constructor
    · rintro (⟨h, -⟩ | ⟨m, u, -, hm, hr0, hrx, hry⟩ | ⟨h, -⟩)
      · exact absurd h hx
      · obtain ⟨h', e⟩ := genCurve_add_of_X_ne h₁ h₂ hx m hm
        rw [e, eq_pointCode_some_iff]
        exact ⟨hr0, hrx, hry⟩
      · exact absurd h hx
    · intro hr
      set m := (y₂ - y₁) / (x₂ - x₁) with hmdef
      have hm : (x₂ - x₁) * m = y₂ - y₁ := by rw [hmdef]; field_simp
      obtain ⟨h', e⟩ := genCurve_add_of_X_ne h₁ h₂ hx m hm
      rw [e, eq_pointCode_some_iff] at hr
      have hN : QuadraticAlgebra.norm (x₂ - x₁) ≠ 0 := fun h0 => hx' (K0.norm_eq_zero_iff.mp h0)
      exact Or.inr (Or.inl ⟨m, _, inv_mul_cancel₀ hN, hm, hr⟩)

/-- **Raw addition on canonical codes** (`model/raw-addition-points.md`): for all
`P, Q ∈ E(K₀)` and `r ∈ ℚ⁵`, `Rel_raw_add(code P, code Q, r) ↔ r = code(P + Q)`. -/
theorem rel_rawAdd_iff (P Q : genCurve.toAffine.Point) (r : Fin 5 → ℚ) :
    rawAddTemplate.Rel (Fin.append (Fin.append (pointCode P) (pointCode Q)) r) ↔
      r = pointCode (P + Q) := by
  rw [rawAddTemplate_rel_iff_spec, rawAddSpec_pointCode_iff]

/-- **Raw addition** (`model/raw-addition.md`): for all `a, b ∈ ℤ` and `R ∈ ℚ⁵`,
`Add_raw(ι(a), ι(b), R) ↔ R = ι(a + b)`. -/
theorem rel_rawAdd_iota (a b : ℤ) (R : Fin 5 → ℚ) :
    rawAddTemplate.Rel (Fin.append (Fin.append (iota a) (iota b)) R) ↔ R = iota (a + b) := by
  rw [iota_def, iota_def, rel_rawAdd_iff, iota_add]

end ZInQ
