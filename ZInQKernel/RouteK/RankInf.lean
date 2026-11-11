import ZInQKernel.RouteK.RankDL
import ZInQKernel.RouteK.RankVariants

/-!
# CR₃ as "`C_d` has infinitely many rational points" (no group law in the trusted text)

The positive-rank hypotheses `RouteK.Rank.CertifiedRankRk`, `CertifiedRankTYZRk`,
`CertifiedRankTYZClRk` (`RouteK/Rank/Statements.lean`) and `CertifiedRankDLRk`
(`RouteK/RankDL.lean`) conclude `∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point,
¬IsOfFinAddOrder P`, so their statements contain Mathlib's group law on `C_d(ℚ)` and its instances.
This module restates them with the conclusion `InfinitelyManyPoints d`: the set of rational
solutions of `y² = x³ − d²x` is infinite. For squarefree `d` this is the classical statement
"`d` is a congruent number".

* `RouteK.Rank.exists_infinite_order_iff_infinitelyManyPoints`: for `d ≠ 0`, `C_d(ℚ)` has a point of
  infinite order iff `InfinitelyManyPoints d` (Mordell–Weil, `fg_points`, and the structure of
  finitely generated torsion abelian groups);
* `CertifiedRankInf`, `CertifiedRankTYZInf`, `CertifiedRankTYZClInf`, `CertifiedRankDLInf`, each
  proved equivalent to its `Rk` form;
* Theorem 1.1 from SixContactMin and each `Inf` form.
-/

namespace ZInQ

namespace RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.RouteK.Selmer ZInQ.RouteK.Rank5b

/-- `C_d : y² = x³ − d²x` has infinitely many rational points (affine solutions `(x, y) ∈ ℚ²`).
For squarefree `d > 0` this is the classical statement "`d` is a congruent number". The
statement mentions no group law. -/
def InfinitelyManyPoints (d : ℕ) : Prop :=
  Set.Infinite {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 - (d : ℚ) ^ 2 * p.1}

/-- An affine rational solution of `y² = x³ − d²x` is a nonsingular point of `C_d` (`d ≠ 0`). -/
theorem infPts_nonsingular {d : ℕ} (hd : d ≠ 0) {p : ℚ × ℚ}
    (hp : p.2 ^ 2 = p.1 ^ 3 - (d : ℚ) ^ 2 * p.1) :
    (shortCurve (-(d : ℚ) ^ 2)).toAffine.Nonsingular p.1 p.2 := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hΔ : (shortCurve (-(d : ℚ) ^ 2)).Δ ≠ 0 := by
    rw [shortCurve_Δ]
    have : (-(d : ℚ) ^ 2) ^ 3 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ hd'))
    exact mul_ne_zero (by norm_num) this
  refine (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_
  rw [shortCurve_equation_iff]
  linear_combination hp

/-- The points of `C_d(ℚ)` are `0` and the affine solutions: `Option` of the solution set maps
bijectively onto the point type. -/
noncomputable def infPtsMap {d : ℕ} (hd : d ≠ 0) :
    Option {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 - (d : ℚ) ^ 2 * p.1} →
      (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point
  | none => 0
  | some p => .some p.1.1 p.1.2 (infPts_nonsingular hd p.2)

theorem infPtsMap_bijective {d : ℕ} (hd : d ≠ 0) : Function.Bijective (infPtsMap hd) := by
  constructor
  · rintro (_ | ⟨⟨⟨x, y⟩, hp⟩⟩) (_ | ⟨⟨⟨x', y'⟩, hp'⟩⟩) h
    · rfl
    · exact absurd h.symm (Point.some_ne_zero _)
    · exact absurd h (Point.some_ne_zero _)
    · simp only [infPtsMap, Point.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · rintro (_ | ⟨x, y, h⟩)
    · exact ⟨none, rfl⟩
    · have hp : y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x := by
        have := (shortCurve_equation_iff _ x y).mp h.1
        linear_combination this
      exact ⟨some ⟨(x, y), hp⟩, rfl⟩

/-- `InfinitelyManyPoints d` iff the point type of `C_d(ℚ)` is infinite (`d ≠ 0`). -/
theorem infinitelyManyPoints_iff_infinite_points {d : ℕ} (hd : d ≠ 0) :
    InfinitelyManyPoints d ↔ Infinite (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point := by
  rw [InfinitelyManyPoints, ← Set.infinite_coe_iff, ← Option.infinite_iff]
  exact (Equiv.ofBijective _ (infPtsMap_bijective hd)).infinite_iff

/-- **Infinite order iff infinitely many points.** For `d ≠ 0`, `C_d(ℚ)` has a point of infinite
order iff `y² = x³ − d²x` has infinitely many rational solutions. One direction: the multiples of a
point of infinite order are pairwise distinct. The other: `C_d(ℚ)` is finitely generated
(`fg_points`), so if every point had finite order it would be finite
(`AddCommGroup.finite_of_fg_isAddTorsion`). -/
theorem exists_infinite_order_iff_infinitelyManyPoints {d : ℕ} (hd : d ≠ 0) :
    (∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P) ↔
      InfinitelyManyPoints d := by
  rw [infinitelyManyPoints_iff_infinite_points hd]
  constructor
  · rintro ⟨P, hP⟩
    exact Infinite.of_injective _ (injective_nsmul_iff_not_isOfFinAddOrder.mpr hP)
  · intro hinf
    by_contra hall
    push Not at hall
    have := fg_points d hd
    have := AddCommGroup.finite_of_fg_isAddTorsion
      (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point hall
    exact not_finite (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point

end RouteK.Rank

end ZInQ
