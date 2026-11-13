import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# tyz-decomp: TYZ's curve `A` and Lemma 3.16 over genuine definitions

Report: `docs/research/tyz-decomp.md` §3. This file states, over Mathlib's definitions, the one
input of the genus-point package of Tian–Yuan–Zhang (TYZ, arXiv:1411.4728v1; Asian J. Math. 21
(2017)) that needs no object missing from Mathlib: **Lemma 3.16** (L2182–2185, quoted from
`nt-tyz.md` §1.2; source not re-read here): `A(ℚ(i)) = A[(1+i)³]`.

* TYZ's `A : 2y² = x³ + x` (§3.1) is `ℚ`-isomorphic to `curveA : y² = x³ + 4x` by
  `(x, y) ↦ (2x, 4y)` (`16y² = 8(x³ + x) = (2x)³ + 4(2x)`). The isomorphism is defined over `ℚ`,
  commutes with `[i] : (x, y) ↦ (−x, iy)` on both models and with `Gal(ℚ̄/ℚ)`, and preserves fields
  of definition, so Lemma 3.16 transfers verbatim.
* `[i]` is the coordinate map `iPt` (with a fixed `i ∈ ℚ̄`, `i² = −1`; the statement is symmetric
  under `i ↦ −i`). `[(1+i)³] = [2]∘[i]∘[1+i]` and `[i]` is an automorphism, so
  `A[(1+i)³] = {P | 2(P + [i]P) = 0}`; this uses only the (standard) additivity of `[i]`, which the
  statement itself does not need.
* `A(K)` for `K ⊆ ℚ̄`: the points with both coordinates in `K` (`IsDefinedOver`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.CurveA

/-- `ℚ̄`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- Classical decidable equality on `ℚ̄` (needed for Mathlib's group law on points). -/
instance : DecidableEq Qbar := Classical.decEq _

/-- `y² = x³ + 4x`, `ℚ`-isomorphic to TYZ's `A : 2y² = x³ + x`. -/
def curveA : WeierstrassCurve ℚ := shortCurve 4

/-- `A` over `ℚ̄`. -/
abbrev curveAbar : WeierstrassCurve Qbar := curveA.baseChange Qbar

/-- `A(ℚ̄)`. -/
abbrev PtA : Type := curveAbar.toAffine.Point

theorem exists_sqrt_neg_one : ∃ i : Qbar, i ^ 2 = -1 :=
  IsAlgClosed.exists_pow_nat_eq (-1) two_pos

/-- A fixed `i ∈ ℚ̄`. -/
def iQ : Qbar := exists_sqrt_neg_one.choose

theorem iQ_sq : iQ ^ 2 = -1 := exists_sqrt_neg_one.choose_spec

theorem iQ_ne_zero : iQ ≠ 0 := by
  intro h
  have := iQ_sq
  rw [h] at this
  norm_num at this

@[simp] theorem curveAbar_a₁ : curveAbar.a₁ = 0 := by
  simp [curveAbar, curveA, WeierstrassCurve.baseChange]
@[simp] theorem curveAbar_a₂ : curveAbar.a₂ = 0 := by
  simp [curveAbar, curveA, WeierstrassCurve.baseChange]
@[simp] theorem curveAbar_a₃ : curveAbar.a₃ = 0 := by
  simp [curveAbar, curveA, WeierstrassCurve.baseChange]
@[simp] theorem curveAbar_a₄ : curveAbar.a₄ = 4 := by
  simp [curveAbar, curveA, WeierstrassCurve.baseChange]
@[simp] theorem curveAbar_a₆ : curveAbar.a₆ = 0 := by
  simp [curveAbar, curveA, WeierstrassCurve.baseChange]

/-- `(x, y) ↦ (−x, iy)` preserves nonsingular points of `y² = x³ + 4x`. -/
theorem nonsingular_iPt {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    curveAbar.toAffine.Nonsingular (-x) (iQ * y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff'] at h ⊢
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * iQ_sq - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : iQ * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 iQ_ne_zero
    · linear_combination h0

/-- **`[i]` on `A(ℚ̄)`**: `O ↦ O`, `(x, y) ↦ (−x, iy)`. -/
def iPt : PtA → PtA
  | .zero => .zero
  | .some x y h => .some (-x) (iQ * y) (nonsingular_iPt h)

theorem iPt_some {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    iPt (.some x y h) = .some (-x) (iQ * y) (nonsingular_iPt h) := rfl

/-- `P ∈ A(K)`: `P = O`, or both coordinates of `P` lie in `K`. -/
def IsDefinedOver (K : IntermediateField ℚ Qbar) : PtA → Prop
  | .zero => True
  | .some x y _ => x ∈ K ∧ y ∈ K

/-- `ℚ(i) ⊆ ℚ̄`. -/
def Qi : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {iQ}

/-- **Leaf TYZ-3.16 (TYZ Lemma 3.16, second assertion)**: `A(ℚ(i)) = A[(1+i)³]`, i.e. a point of
`A(ℚ̄)` is defined over `ℚ(i)` iff `2(P + [i]P) = 0`. TYZ L2182–2185 (arXiv v1; journal number
UNVERIFIED). Refereed. Used by the package field `GenusData.β_τ` (`β'` fixes `A[(1+i)³]` because
it fixes `ℚ(i)`, L2581) and, with Lemma 3.18, by `GenusData.tors_mem_range`. -/
def TYZLemma316 : Prop :=
  ∀ P : PtA, IsDefinedOver Qi P ↔ 2 • (P + iPt P) = 0

/-- Sanity check (non-vacuity of the right-hand side): `O` satisfies both sides. -/
theorem lemma316_zero : IsDefinedOver Qi (0 : PtA) ∧ 2 • ((0 : PtA) + iPt 0) = 0 := by
  have h0 : iPt (0 : PtA) = 0 := rfl
  exact ⟨trivial, by rw [h0, add_zero, nsmul_zero]⟩

/-! ### `[i]` is an additive automorphism with `[i]² = −1` (§4.2 item 1 of the report)

Not used by the glue; first step towards a genuine-ambient genus-point package. -/

open WeierstrassCurve.Affine in
theorem slope_iPt (x₁ x₂ y₁ y₂ : Qbar) :
    curveAbar.toAffine.slope (-x₁) (-x₂) (iQ * y₁) (iQ * y₂) =
      -iQ * curveAbar.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hi := iQ_sq
  have hi0 := iQ_ne_zero
  by_cases hx : x₁ = x₂
  · have hx' : -x₁ = -x₂ := by rw [hx]
    by_cases hy : y₁ = curveAbar.toAffine.negY x₂ y₂
    · have hy' : iQ * y₁ = curveAbar.toAffine.negY (-x₂) (iQ * y₂) := by
        simp only [negY, curveAbar_a₁, curveAbar_a₃] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy', mul_zero]
    · have hy' : iQ * y₁ ≠ curveAbar.toAffine.negY (-x₂) (iQ * y₂) := by
        simp only [negY, curveAbar_a₁, curveAbar_a₃] at hy ⊢
        intro h
        apply hy
        have : iQ * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hi0
        · linear_combination h0
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      simp only [negY, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄]
      have key : ∀ A : Qbar, A / (2 * iQ * y₁) = -iQ * (A / (2 * y₁)) := by
        intro A
        rcases eq_or_ne y₁ 0 with h0 | h0
        · simp [h0]
        · field_simp
          linear_combination A * hi
      convert key (3 * x₁ ^ 2 + 4) using 2 <;> ring
  · have hx' : -x₁ ≠ -x₂ := fun h => hx (neg_injective h)
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    rw [show -x₁ - -x₂ = -(x₁ - x₂) by ring, div_neg, show iQ * y₁ - iQ * y₂ = iQ * (y₁ - y₂) by ring]
    ring

open WeierstrassCurve.Affine in
/-- **`[i]` is additive.** -/
theorem iPt_add (P Q : PtA) : iPt (P + Q) = iPt P + iPt Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · have hi := iQ_sq
    have hi0 := iQ_ne_zero
    by_cases hxy : x₁ = x₂ ∧ y₁ = curveAbar.toAffine.negY x₂ y₂
    · have hxy' : -x₁ = -x₂ ∧ iQ * y₁ = curveAbar.toAffine.negY (-x₂) (iQ * y₂) := by
        refine ⟨by rw [hxy.1], ?_⟩
        have := hxy.2
        simp only [negY, curveAbar_a₁, curveAbar_a₃] at this ⊢
        rw [this]; ring
      rw [Point.add_of_Y_eq hxy.1 hxy.2, iPt_some, iPt_some, Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(-x₁ = -x₂ ∧ iQ * y₁ = curveAbar.toAffine.negY (-x₂) (iQ * y₂)) := by
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨neg_injective h1, ?_⟩
        simp only [negY, curveAbar_a₁, curveAbar_a₃] at h2 ⊢
        have : iQ * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hi0
        · linear_combination h0
      rw [Point.add_some hxy, iPt_some, iPt_some, iPt_some, Point.add_some hxy', Point.some.injEq]
      have hs := slope_iPt x₁ x₂ y₁ y₂
      constructor
      · simp only [addX, curveAbar_a₁, curveAbar_a₂]
        rw [hs]
        linear_combination (-(curveAbar.toAffine.slope x₁ x₂ y₁ y₂) ^ 2) * hi
      · simp only [addY, negAddY, addX, negY, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
        rw [hs]
        linear_combination (-iQ * curveAbar.toAffine.slope x₁ x₂ y₁ y₂ ^ 3) * hi

/-- `[i]` as an additive endomorphism of `A(ℚ̄)`. -/
def iHom : PtA →+ PtA := AddMonoidHom.mk' iPt iPt_add

/-- **`[i]² = −1`.** -/
theorem iPt_iPt (P : PtA) : iPt (iPt P) = -P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [iPt_some, iPt_some, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨neg_neg x, ?_⟩
    simp only [WeierstrassCurve.Affine.negY, curveAbar_a₁, curveAbar_a₃]
    linear_combination y * iQ_sq

/-- `[i]` as an element of the ring `End(A(ℚ̄))`. -/
def iEnd : AddMonoid.End PtA := AddMonoidHom.mk' iPt iPt_add

theorem iEnd_apply (P : PtA) : iEnd P = iPt P := rfl

end ZInQ.Contrib.TYZDecomp.CurveA

#print axioms ZInQ.Contrib.TYZDecomp.CurveA.nonsingular_iPt
#print axioms ZInQ.Contrib.TYZDecomp.CurveA.lemma316_zero
#print axioms ZInQ.Contrib.TYZDecomp.CurveA.iPt_add
#print axioms ZInQ.Contrib.TYZDecomp.CurveA.iPt_iPt
