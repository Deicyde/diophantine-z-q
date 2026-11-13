import ZInQKernel.Model.Descent.Kummer

/-!
# The two-torsion of `C_d : y² = x³ - d² x` over `ℚ`

`C_d(ℚ)[2] = {O, (0,0), (d,0), (-d,0)}`, a group of order four (`twoTorsion_card`); the
membership criterion is `mwTwoTorsion_iff`.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

theorem mwIsElliptic (d : ℕ) (hd : d ≠ 0) : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic :=
  shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 (by exact_mod_cast hd)))

theorem mwTwoTorsion_nonsingular (d : ℕ) (hd : d ≠ 0) {e : ℚ} (he : e = 0 ∨ e = d ∨ e = -d) :
    (shortCurve (-(d : ℚ) ^ 2)).toAffine.Nonsingular e 0 := by
  have := mwIsElliptic d hd
  refine equation_iff_nonsingular.mp ?_
  rw [shortCurve_equation_iff]
  rcases he with rfl | rfl | rfl <;> ring

/-- The two-torsion point `(e, 0)` of `C_d`, `e ∈ {0, d, -d}`. -/
def mwTwoTorsionPt (d : ℕ) (hd : d ≠ 0) (e : ℚ) (he : e = 0 ∨ e = d ∨ e = -d) :
    (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point :=
  .some e 0 (mwTwoTorsion_nonsingular d hd he)

/-- **Two-torsion of `C_d(ℚ)`**: `2P = O` iff `P ∈ {O, (0,0), (d,0), (-d,0)}`. -/
theorem mwTwoTorsion_iff (d : ℕ) (hd : d ≠ 0) (P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) :
    2 • P = 0 ↔ P = 0 ∨ P = mwTwoTorsionPt d hd 0 (Or.inl rfl) ∨
      P = mwTwoTorsionPt d hd d (Or.inr (Or.inl rfl)) ∨
      P = mwTwoTorsionPt d hd (-d) (Or.inr (Or.inr rfl)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true (nsmul_zero 2) (Or.inl rfl)
  rw [shortCurve_two_nsmul_some_eq_zero_iff]
  simp only [mwTwoTorsionPt, Point.some.injEq]
  constructor
  · rintro rfl
    have he := (shortCurve_equation_iff _ x 0).mp h.1
    have : x * (x - d) * (x + d) = 0 := by linear_combination -he
    have h0 : ¬(Point.some x 0 h = 0) := Point.some_ne_zero h
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inr (Or.inl ⟨h2, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨sub_eq_zero.mp h2, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨eq_neg_of_add_eq_zero_left h1, rfl⟩))
  · rintro (h0 | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩)
    · exact absurd h0 (Point.some_ne_zero h)
    all_goals rfl

/-- **`#C_d(ℚ)[2] = 4`**. -/
theorem twoTorsion_card (d : ℕ) (hd : d ≠ 0) :
    Nat.card {P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point // 2 • P = 0} = 4 := by
  classical
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  set S : Finset (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point :=
    {0, mwTwoTorsionPt d hd 0 (Or.inl rfl), mwTwoTorsionPt d hd d (Or.inr (Or.inl rfl)),
      mwTwoTorsionPt d hd (-d) (Or.inr (Or.inr rfl))} with hS
  have hmem : ∀ P, 2 • P = 0 ↔ P ∈ S := by
    intro P
    rw [mwTwoTorsion_iff d hd P, hS]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card, Fintype.card_coe,
    hS]
  have h1 : (d : ℚ) ≠ -d := by intro h; apply hd'; linarith
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · simp only [mwTwoTorsionPt, ne_eq, Point.some.injEq, and_true]; exact h1
  · simp only [mwTwoTorsionPt, Finset.mem_insert, Finset.mem_singleton, Point.some.injEq,
      and_true, not_or]
    exact ⟨fun h => hd' h.symm, by intro h; apply hd'; linarith⟩
  · simp only [mwTwoTorsionPt, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => Point.some_ne_zero _ h.symm, fun h => Point.some_ne_zero _ h.symm,
      fun h => Point.some_ne_zero _ h.symm⟩

end ZInQ.RouteK.Rank
