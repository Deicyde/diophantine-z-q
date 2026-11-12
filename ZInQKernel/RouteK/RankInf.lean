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

/-! ### The four hypotheses with the conclusion "infinitely many rational points" -/

/-- **Hypothesis CR₃^Inf** (CR₃^Rk with the conclusion "infinitely many rational points"). Let
`d > 0` be squarefree with `d ≡ 5 (mod 8)`. If `Sel₂(C_d)` (`Sel2 d`) has exactly 8 elements and
contains a pair `(a, b)` with `|a| ≡ 7 (mod 8)`, then `y² = x³ − d²x` has infinitely many rational
solutions, i.e. `d` is a congruent number.

**Trust statement.** Not proved in Lean. It has the same strength as `CertifiedRankRk`
(`certifiedRankInf_iff_certifiedRankRk`) and rests on the same literature (Tian–Yuan–Zhang with
Proposition N, and Gross–Zagier with an auxiliary field; see `CertifiedRankRk`). It differs only in
that the trusted statement mentions no group law: its conclusion is `InfinitelyManyPoints d`. -/
def CertifiedRankInf : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) →
    InfinitelyManyPoints d

/-- **Hypothesis CR₃^TYZ,Inf** (CR₃^TYZ,Rk with the conclusion "infinitely many rational points").
For squarefree `d ≡ 5 (mod 8)` with odd genus sum `T5b d` (`Rank5b.T5b`, Rédei bits),
`y² = x³ − d²x` has infinitely many rational solutions (`d` is a congruent number).

**Trust statement.** Not proved in Lean. Same strength as `CertifiedRankTYZRk`
(`certifiedRankTYZInf_iff_certifiedRankTYZRk`), resting on Tian–Yuan–Zhang with Gross–Zagier (see
`CertifiedRankTYZRk`); the trusted statement mentions no group law. -/
def CertifiedRankTYZInf : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5b d = 1 → InfinitelyManyPoints d

/-- **Hypothesis CR₃^TYZ_Cl,Inf** (CR₃^TYZ_Cl,Rk with the conclusion "infinitely many rational
points"). For squarefree `d ≡ 5 (mod 8)` with odd genus sum of class numbers
`T5bCl d = Σ_π Π_{B∈π} #(2 Cl(ℚ(√−d_B)))`, `y² = x³ − d²x` has infinitely many rational solutions
(`d` is a congruent number).

**Trust statement.** Not proved in Lean. Same strength as `CertifiedRankTYZClRk`
(`certifiedRankTYZClInf_iff_certifiedRankTYZClRk`), resting on Tian–Yuan–Zhang (arXiv:1411.4728)
with Gross–Zagier (see `CertifiedRankTYZClRk`); the trusted statement mentions no group law. -/
def CertifiedRankTYZClInf : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 → InfinitelyManyPoints d

/-- **Hypothesis CR₃^DL,Inf** (CR₃^DL,Rk with the conclusion "infinitely many rational points").
For all `β`, `θ`, `p₀` satisfying the slot inputs `RouteK.Inputs β θ p₀` there is a slot choice
`D : RouteK.Slots β θ p₀` such that both `y² = x³ − d₁²x` and `y² = x³ − (d₁ |θ|)²x`
(`d₁ = D.d₁`) have infinitely many rational solutions.

**Trust statement.** Not proved in Lean. Same strength as `CertifiedRankDLRk`
(`certifiedRankDLInf_iff_certifiedRankDLRk`), implied by CR₃^Inf and CR₃^TYZ,Inf through the `Rk`
forms; the trusted statement mentions no group law, but like `CertifiedRankDLRk` it depends on the
internal definitions `RouteK.Inputs` and `RouteK.Slots`. -/
def CertifiedRankDLInf : Prop :=
  ∀ (β θ : ℤ) (p₀ : ℕ), Inputs β θ p₀ → ∃ D : Slots β θ p₀,
    InfinitelyManyPoints D.d₁ ∧ InfinitelyManyPoints (D.d₁ * θ.natAbs)

/-- CR₃^Inf and CR₃^Rk are equivalent (`exists_infinite_order_iff_infinitelyManyPoints`). -/
theorem certifiedRankInf_iff_certifiedRankRk : CertifiedRankInf ↔ CertifiedRankRk :=
  forall_congr' fun d => forall_congr' fun hd5 => by
    simp only [exists_infinite_order_iff_infinitelyManyPoints (ne_zero_of_mod_eight_eq_five hd5)]

/-- CR₃^TYZ,Inf and CR₃^TYZ,Rk are equivalent. -/
theorem certifiedRankTYZInf_iff_certifiedRankTYZRk : CertifiedRankTYZInf ↔ CertifiedRankTYZRk :=
  forall_congr' fun d => forall_congr' fun hd5 => by
    simp only [exists_infinite_order_iff_infinitelyManyPoints (ne_zero_of_mod_eight_eq_five hd5)]

/-- CR₃^TYZ_Cl,Inf and CR₃^TYZ_Cl,Rk are equivalent. -/
theorem certifiedRankTYZClInf_iff_certifiedRankTYZClRk :
    CertifiedRankTYZClInf ↔ CertifiedRankTYZClRk :=
  forall_congr' fun d => forall_congr' fun hd5 => by
    simp only [exists_infinite_order_iff_infinitelyManyPoints (ne_zero_of_mod_eight_eq_five hd5)]

/-- CR₃^DL,Inf and CR₃^DL,Rk are equivalent: both slot curves have `d ≡ 5 (mod 8)`, so `d ≠ 0`. -/
theorem certifiedRankDLInf_iff_certifiedRankDLRk : CertifiedRankDLInf ↔ CertifiedRankDLRk := by
  refine forall_congr' fun β => forall_congr' fun θ => forall_congr' fun p₀ =>
    forall_congr' fun hI => exists_congr fun D => ?_
  rw [exists_infinite_order_iff_infinitelyManyPoints
      (ne_zero_of_mod_eight_eq_five (D.d₁_mod hI)),
    exists_infinite_order_iff_infinitelyManyPoints
      (ne_zero_of_mod_eight_eq_five (slots_d₂_facts D hI).1)]

end RouteK.Rank

/-- **Theorem 1.1** from 6C_min and CR₃^Inf (`RouteK.Rank.CertifiedRankInf`), through
CR₃^Rk. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankInf
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankInf) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk hH
    (RouteK.Rank.certifiedRankInf_iff_certifiedRankRk.mp hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^TYZ,Inf (`RouteK.Rank.CertifiedRankTYZInf`), through
CR₃^TYZ,Rk. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZInf
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankTYZInf) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk hH
    (RouteK.Rank.certifiedRankTYZInf_iff_certifiedRankTYZRk.mp hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^TYZ_Cl,Inf (`RouteK.Rank.CertifiedRankTYZClInf`), through
CR₃^TYZ_Cl,Rk. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClInf
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankTYZClInf) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk hH
    (RouteK.Rank.certifiedRankTYZClInf_iff_certifiedRankTYZClRk.mp hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^DL,Inf (`RouteK.Rank.CertifiedRankDLInf`), through
CR₃^DL,Rk. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLInf
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankDLInf) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk hH
    (RouteK.Rank.certifiedRankDLInf_iff_certifiedRankDLRk.mp hCR)

end ZInQ
