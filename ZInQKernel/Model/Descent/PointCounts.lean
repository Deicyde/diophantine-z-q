import ZInQKernel.Model.Field.ShortWeierstrass
import ZInQKernel.Hypotheses.PrimePattern

/-!
# Point counts at `(17, s - 6)` and `(23, s - 5)`

Blueprint: `model/descent/reduction-point-counts.md`.

`6² ≡ 2 (mod 17)`, `5² ≡ 2 (mod 23)`; `d ↦ 12`, `-d² ↦ -8` modulo `17` and `d ↦ 17`,
`-d² ↦ -13` modulo `23`; the curves `y² = x³ - 8x` over `𝔽₁₇` and `y² = x³ - 13x` over `𝔽₂₃`
have `19` and `23` affine points, hence `20` and `24` points. All checked by `decide` in the
kernel.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance fact_prime_23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- The closed statements of the point-count article. -/
theorem pointCounts_17_23 :
    (6 : ZMod 17) ^ 2 = 2 ∧ (5 : ZMod 23) ^ 2 = 2 ∧
    (75 - 53 * 6 : ZMod 17) = 12 ∧ (-(75 - 53 * 6) ^ 2 : ZMod 17) = -8 ∧ (-8 : ZMod 17) ≠ 0 ∧
    (75 - 53 * 5 : ZMod 23) = 17 ∧ (-(75 - 53 * 5) ^ 2 : ZMod 23) = -13 ∧ (-13 : ZMod 23) ≠ 0 ∧
    (Finset.univ.filter (fun xy : ZMod 17 × ZMod 17 => xy.2 ^ 2 = xy.1 ^ 3 - 8 * xy.1)).card = 19 ∧
    (Finset.univ.filter (fun xy : ZMod 23 × ZMod 23 => xy.2 ^ 2 = xy.1 ^ 3 - 13 * xy.1)).card = 23 := by
  decide

/-- The number of affine points of `y² = x³ + a x` over `ZMod p` as a `Finset` count. -/
theorem card_affine_eq_filter (p : ℕ) [NeZero p] (a : ZMod p) :
    Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1} =
      (Finset.univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem pointCount_17 : pointCount 17 (-8) = 20 := by
  rw [pointCount, card_affine_eq_filter]
  have := pointCounts_17_23.2.2.2.2.2.2.2.2.1
  simp only [neg_mul, ← sub_eq_add_neg]
  rw [this]

theorem pointCount_23 : pointCount 23 (-13) = 24 := by
  rw [pointCount, card_affine_eq_filter]
  have := pointCounts_17_23.2.2.2.2.2.2.2.2.2
  simp only [neg_mul, ← sub_eq_add_neg]
  rw [this]

/-- The group order of `y² = x³ + a x` over `ZMod p` is `pointCount p a`. -/
theorem card_point_shortCurve (p : ℕ) [Fact p.Prime] (a : ZMod p) [(shortCurve a).IsElliptic] :
    Nat.card (shortCurve a).toAffine.Point = pointCount p a := by
  rw [Nat.card_congr (pointEquiv (shortCurve a).toAffine), pointCount]
  rw [show Nat.card (WithZero {xy : ZMod p × ZMod p // (shortCurve a).toAffine.Equation xy.1 xy.2}) =
      Nat.card (Option {xy : ZMod p × ZMod p // (shortCurve a).toAffine.Equation xy.1 xy.2}) from rfl,
    Nat.card_congr (Equiv.optionEquivSumPUnit.{0, 0} _), Nat.card_sum, Nat.card_eq_fintype_card (α := PUnit),
    Fintype.card_punit]
  congr 1
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun (xy : ZMod p × ZMod p) => shortCurve_equation_iff a xy.1 xy.2)

instance : NeZero (2 : ZMod 17) := ⟨by decide⟩
instance : NeZero (2 : ZMod 23) := ⟨by decide⟩

instance shortCurve_17_isElliptic : (shortCurve (-8 : ZMod 17)).IsElliptic :=
  shortCurve_isElliptic (by decide)

instance shortCurve_23_isElliptic : (shortCurve (-13 : ZMod 23)).IsElliptic :=
  shortCurve_isElliptic (by decide)

/-- `#Ẽ(𝔽₁₇) = 20` for `Ẽ : y² = x³ - 8x`. -/
theorem card_point_17 : Nat.card (shortCurve (-8 : ZMod 17)).toAffine.Point = 20 := by
  rw [card_point_shortCurve, pointCount_17]

/-- `#Ẽ(𝔽₂₃) = 24` for `Ẽ : y² = x³ - 13x`. -/
theorem card_point_23 : Nat.card (shortCurve (-13 : ZMod 23)).toAffine.Point = 24 := by
  rw [card_point_shortCurve, pointCount_23]

end ZInQ
