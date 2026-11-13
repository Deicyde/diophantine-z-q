import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.Package
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM WeierstrassCurve.Affine

theorem iPt_ptT_eq : iPt ptT = .some (-2) (-4 * iQ) (by
    have := nonsingular_iPt nonsingular_T
    convert this using 1; ring) := by
  rw [ptT, iPt_some, Point.some.injEq]; constructor <;> ring

theorem nonsingular_m2iQ : curveAbar.toAffine.Nonsingular (-2 * iQ) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  have hi := iQ_sq
  refine ⟨by linear_combination (8 * iQ) * hi, Or.inl ?_⟩
  intro h
  have : (8 : Qbar) = 0 := by linear_combination h + 12 * hi
  norm_num at this

/-- `τ((1+i)/2) = T + [i]T = (−2i, 0)`. -/
theorem ptT_add_iPt_ptT : ptT + iPt ptT = .some (-2 * iQ) 0 nonsingular_m2iQ := by
  rw [iPt_ptT_eq, ptT]
  have hx : (2 : Qbar) ≠ -2 := by norm_num
  rw [Point.add_of_X_ne hx, Point.some.injEq]
  have hi := iQ_sq
  have hs : curveAbar.toAffine.slope 2 (-2) (-4) (-4 * iQ) = -1 + iQ := by
    rw [slope_of_X_ne hx]
    field_simp
    ring
  simp only [addX, addY, negAddY, negY, hs, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor
  · linear_combination hi
  · linear_combination (3 - iQ) * hi

theorem iPt_some_m2iQ : iPt (.some (-2 * iQ) 0 nonsingular_m2iQ) =
    .some (2 * iQ) 0 (by
      have := nonsingular_iPt nonsingular_m2iQ
      convert this using 1 <;> ring) := by
  rw [iPt_some, Point.some.injEq]; constructor <;> ring

/-- **The eight points of `A[(1+i)³]` (x0-32's `X0.IsTorsI3`) are values of the pinned `τ`.** -/
theorem isTorsI3_mem_range (P : PtA) (h : X0.IsTorsI3 P) : ∃ y : GaussianInt, tauG y = P := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨0, map_zero tauG⟩
  simp only [X0.IsTorsI3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact ⟨⟨2, 0⟩, by rw [tauG_mk, two_zsmul_ptT, zero_zsmul, add_zero]; rfl⟩
  · exact ⟨⟨-1, 0⟩, by rw [tauG_mk, neg_one_zsmul, zero_zsmul, add_zero, neg_ptT]⟩
  · exact ⟨⟨1, 0⟩, by rw [tauG_mk, one_zsmul, zero_zsmul, add_zero]; rfl⟩
  · refine ⟨⟨0, -1⟩, ?_⟩
    rw [tauG_mk, neg_one_zsmul, zero_zsmul, zero_add, iPt_ptT_eq, Point.neg_some, Point.some.injEq]
    simp only [negY, curveAbar_a₁, curveAbar_a₃]
    exact ⟨trivial, by ring⟩
  · exact ⟨⟨0, 1⟩, by rw [tauG_mk, one_zsmul, zero_zsmul, zero_add, iPt_ptT_eq]⟩
  · refine ⟨⟨1, -1⟩, ?_⟩
    have e : ptT - iPt ptT = -iPt (ptT + iPt ptT) := by rw [iPt_add, iPt_iPt]; abel
    rw [tauG_mk, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, e, ptT_add_iPt_ptT, iPt_some_m2iQ,
      Point.neg_some, Point.some.injEq]
    simp only [negY, curveAbar_a₁, curveAbar_a₃]
    exact ⟨trivial, by ring⟩
  · exact ⟨⟨1, 1⟩, by rw [tauG_mk, one_zsmul, one_zsmul, ptT_add_iPt_ptT]⟩

theorem gi_smul (P : PtA) : (ZInQ.PropN.gi : GaussianInt) • P = iPt P := by
  have h1 : (ZInQ.PropN.gi).re = 0 := rfl
  have h2 : (ZInQ.PropN.gi).im = 1 := rfl
  rw [gsmul_def, h1, h2, zero_zsmul, one_zsmul, zero_add]

/-- `2(P + [i]P) = (2 + 2i)•P`. -/
theorem two_nsmul_add_iPt (P : PtA) : 2 • (P + iPt P) = (ZInQ.PropN.twoTwoI : GaussianInt) • P := by
  rw [gsmul_def]
  show 2 • (P + iPt P) = (2 : ℤ) • P + (2 : ℤ) • iPt P
  rw [two_nsmul, two_zsmul, two_zsmul]; abel

/-- **Leaf TYZ-3.18, literal form**: for squarefree `n ≡ 5 (mod 8)`, `A(ℍ'_n)_tors ⊆ A[(1+i)³]`,
i.e. every torsion point `P` of `A(ℍ'_n)` satisfies `2(P + [i]P) = 0`. TYZ Lemma 3.18 (L2230–2232),
literally (no `τ`); refereed. Equivalent to `Lemma318` (`lemma318_iff_literal`). -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

/-- **`Lemma318` (with the pinned `τ`) is TYZ's literal Lemma 3.18**: `τ(½ℤ[i]) = A[(1+i)³]`, by
x0-32's explicit list `X0.two_nsmul_add_iPt_eq_zero_iff` and `tauG_eq_zero`. So the leaf does not
depend on TYZ's fact (1) about `τ`. -/
theorem lemma318_iff_literal (Hn : ℕ → IntermediateField ℚ Qbar) :
    Lemma318 Hn ↔ Lemma318Literal Hn := by
  constructor
  · intro h n hn hsq P hP ht
    obtain ⟨y, rfl⟩ := h n hn hsq P hP ht
    rw [two_nsmul_add_iPt, tauG_apply, smul_smul, ← tauG_apply, tauG_eq_zero]
    exact Dvd.intro y rfl
  · intro h n hn hsq P hP ht
    exact isTorsI3_mem_range P ((X0.two_nsmul_add_iPt_eq_zero_iff P).mp (h n hn hsq P hP ht))

end ZInQ.Contrib.TYZGenus.Package
