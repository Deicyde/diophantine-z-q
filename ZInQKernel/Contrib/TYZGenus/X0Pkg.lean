import ZInQKernel.Contrib.TYZGenus.Package

/-!
# x0-32: `τ(½ℤ[i]) = A[(1+i)³]` explicitly (bridge to cm-points' `Package.lean`)

Owner: task x0-32. Report: `docs/research/x0-32.md`. Written against `TYZGenus/Package.lean` of task
cm-points at commit ba214e17 (merged into wip/x0-32).

cm-points pins TYZ's `τ : ½ℤ[i]/(1+i)ℤ[i] → A[(1+i)³]` as `Package.tauG y = y • (2, −4)`. Here:
the range of `tauG` is exactly x0-32's explicit `IsTorsI3` (`O, (0,0), (2,±4), (−2,±4i), (±2i,0)`),
i.e. `{P | 2(P + [i]P) = 0}` (`tauG_range_iff`), so the leaf `Package.Lemma318` is equivalent to the
statement without `τ`: every torsion point of `A(ℍ'_n)` lies in `A[(1+i)³]` (`lemma318_iff`). That
form is TYZ Lemmas 3.16 + 3.18 alone, without Tian's description of `τ` (TYZ L1386–1399).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.X0

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
open WeierstrassCurve.Affine

/-- Every `y • T` lies in `A[(1+i)³]`. -/
theorem two_nsmul_add_iPt_tauG (y : GaussianInt) :
    2 • (tauG y + iPt (tauG y)) = 0 := by
  rw [tauG_apply, gsmul_def, iPt_add, iPt_zsmul, iPt_zsmul, iPt_iPt]
  have hT2 := two_zsmul_ptT
  have hiT2 := two_zsmul_iPt_ptT
  have key : 2 • (y.re • ptT + y.im • iPt ptT + (y.re • iPt ptT + y.im • -ptT)) =
      (y.re - y.im) • ((2 : ℤ) • ptT) + (y.re + y.im) • ((2 : ℤ) • iPt ptT) := by
    module
  rw [key, hT2, hiT2, ← add_zsmul]
  have : (y.re - y.im + (y.re + y.im)) • pt00 = y.re • (pt00 + pt00) := by
    rw [← two_zsmul, smul_smul]; congr 1; ring
  rw [this, pt00_add_self, zsmul_zero]

theorem nonsingular_m2i0 : curveAbar.toAffine.Nonsingular (-2 * iQ) 0 := by
  rw [nonsingular_iff', equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  have hi := iQ_sq
  refine ⟨by linear_combination (8 * iQ) * hi, Or.inl ?_⟩
  intro h
  have : (8 : Qbar) = 0 := by linear_combination h + 12 * hi
  norm_num at this

theorem nonsingular_2i0 : curveAbar.toAffine.Nonsingular (2 * iQ) 0 := by
  rw [nonsingular_iff', equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  have hi := iQ_sq
  refine ⟨by linear_combination (-8 * iQ) * hi, Or.inl ?_⟩
  intro h
  have : (8 : Qbar) = 0 := by linear_combination h + 12 * hi
  norm_num at this

/-- `(1 + i)T = (−2i, 0)`. -/
theorem tauG_one_add_I : tauG ⟨1, 1⟩ = .some (-2 * iQ) 0 nonsingular_m2i0 := by
  rw [tauG_apply, gsmul_def]
  simp only [one_zsmul]
  rw [ptT, iPt_some]
  have hx : (2 : Qbar) ≠ -2 := by norm_num
  rw [Point.add_of_X_ne hx, Point.some.injEq]
  have hs : curveAbar.toAffine.slope 2 (-2) (-4) (iQ * -4) = -1 + iQ := by
    rw [slope_of_X_ne hx]; norm_num; ring
  have hi := iQ_sq
  simp only [addX, addY, negAddY, negY, hs, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor
  · linear_combination hi
  · linear_combination (3 - iQ) * hi

/-- `(1 − i)T = (2i, 0)`. -/
theorem tauG_one_sub_I : tauG ⟨1, -1⟩ = .some (2 * iQ) 0 nonsingular_2i0 := by
  rw [tauG_apply, gsmul_def]
  simp only [one_zsmul, neg_one_zsmul]
  rw [ptT, iPt_some, Point.neg_some]
  have hx : (2 : Qbar) ≠ -2 := by norm_num
  rw [Point.add_of_X_ne hx, Point.some.injEq]
  have hs : curveAbar.toAffine.slope 2 (-2) (-4) (curveAbar.toAffine.negY (-2) (iQ * -4)) =
      -1 - iQ := by
    rw [slope_of_X_ne hx]; simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
  have hi := iQ_sq
  simp only [addX, addY, negAddY]
  rw [hs]
  simp only [negY, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor
  · linear_combination hi
  · linear_combination (3 + iQ) * hi

theorem some_eq_some {x y x' y' : Qbar} (h : curveAbar.toAffine.Nonsingular x y)
    (h' : curveAbar.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    (Point.some x y h : PtA) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

/-- **`τ(½ℤ[i]) = A[(1+i)³]`**: the range of cm-points' `tauG` is x0-32's explicit eight-point set. -/
theorem tauG_range_iff (P : PtA) : (∃ y : GaussianInt, tauG y = P) ↔ IsTorsI3 P := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (two_nsmul_add_iPt_eq_zero_iff _).mp (two_nsmul_add_iPt_tauG y)
  intro h
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨0, map_zero _⟩
  simp only [IsTorsI3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · refine ⟨2, ?_⟩
    rw [tauG_apply, show (2 : GaussianInt) • ptT = (2 : ℤ) • ptT from ?_, two_zsmul_ptT]
    · rfl
    · rw [gsmul_def]; simp
  · refine ⟨-1, ?_⟩
    rw [tauG_apply, show (-1 : GaussianInt) • ptT = -ptT from ?_, neg_ptT]
    · rw [gsmul_def]; simp
  · exact ⟨1, by rw [tauG_apply, one_smul]; rfl⟩
  · refine ⟨⟨0, -1⟩, ?_⟩
    rw [tauG_apply, gsmul_def]
    simp only [neg_one_zsmul]
    rw [ptT, iPt_some, Point.neg_some]
    apply some_eq_some
    · ring
    · simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
  · refine ⟨⟨0, 1⟩, ?_⟩
    rw [tauG_apply, gsmul_def]
    simp only [one_zsmul]
    rw [ptT, iPt_some]
    apply some_eq_some <;> ring
  · exact ⟨⟨1, -1⟩, tauG_one_sub_I⟩
  · exact ⟨⟨1, 1⟩, tauG_one_add_I⟩

/-- **`Package.Lemma318` without `τ`**: it is equivalent to "every torsion point of `A(ℍ'_n)` lies in
`A[(1+i)³]`" (TYZ Lemmas 3.16 + 3.18, without Tian's description of `τ`). -/
theorem lemma318_iff (Hn : ℕ → IntermediateField ℚ Qbar) :
    Lemma318 Hn ↔ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0 := by
  simp only [Lemma318, tauG_range_iff, two_nsmul_add_iPt_eq_zero_iff]

end ZInQ.Contrib.TYZGenus.X0
