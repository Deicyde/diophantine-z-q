import Mathlib

/-!
# bp-modcurves, layer 0: the moduli interpretation of `Y₁(N)` at the level of points

Over a field `K`, a pair `(E, P)` with `E` a Weierstrass curve and `P ∈ E(K)` an affine point with
`2P ≠ 0` and `3P ≠ 0` is isomorphic, by a unique change of variables sending `P` to `(0, 0)`, to a
curve in **Tate normal form**

  `E(b, c) : y² + (1 − c)xy − by = x³ − bx²`,  `P = (0, 0)`.

(STANDARD: Kubert, Proc. LMS 33 (1976), Table 3; Husemöller, *Elliptic curves*, §4.4;
UNVERIFIED locators.) Consequently, for `N ≥ 4`, `Y₁(N)(K)` (pairs `(E, P)` with `P` of exact
order `N`, up to isomorphism) is in bijection with the `(b, c) ∈ K²` with `Δ(b, c) ≠ 0` and `(0,0)` of
exact order `N` on `E(b, c)`; this is the explicit model of `Y₁(N)` over `ℚ` used in node MC2 of
`docs/research/bp-modcurves.md`.

Over Mathlib's `WeierstrassCurve`, `WeierstrassCurve.VariableChange`, `WeierstrassCurve.Affine.Point`.
A change of variables `C = (u, r, s, t)` is `x = u²x' + r`, `y = u³y' + u²sx' + t`, so it sends
`(x₀, y₀)` to `(0, 0)` exactly when `r = x₀` and `t = y₀`.
-/

namespace BPModCurves

open WeierstrassCurve

variable {K : Type*} [Field K]

/-- The Tate normal form `E(b, c) : y² + (1 − c)xy − by = x³ − bx²`. -/
def tateNF (b c : K) : WeierstrassCurve K := ⟨1 - c, -b, -b, 0, 0⟩

theorem tateNF_equation_zero (b c : K) : (tateNF b c).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp [tateNF]

/-- **Existence of the Tate normal form**, in coordinates: if `(x₀, y₀)` lies on `W`, is not
`2`-torsion (`y₀ ≠ −y₀ − a₁x₀ − a₃`) and not a flex (`x(2P) ≠ x₀`), then a change of variables
sending `(x₀, y₀)` to `(0, 0)` takes `W` to some `E(b, c)`. -/
theorem exists_tateNF_coord [DecidableEq K] (W : WeierstrassCurve K) (x₀ y₀ : K)
    (heq : W.toAffine.Equation x₀ y₀) (h2 : y₀ ≠ W.toAffine.negY x₀ y₀)
    (h3 : W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ y₀ y₀) ≠ x₀) :
    ∃ (C : VariableChange K) (b c : K), C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀ := by
  rw [Affine.equation_iff] at heq
  set d := 2 * y₀ + W.a₁ * x₀ + W.a₃ with hd
  have hd0 : d ≠ 0 := by
    intro h; apply h2; simp only [Affine.negY]; linear_combination h
  set ℓ := (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) / d with hℓ
  have hsl : W.toAffine.slope x₀ x₀ y₀ y₀ = ℓ := by
    rw [Affine.slope_of_Y_ne rfl h2]; simp only [Affine.negY, hℓ, hd]; congr 1; ring
  set A2 := W.a₂ - ℓ * W.a₁ + 3 * x₀ - ℓ ^ 2 with hA2
  have hA20 : A2 ≠ 0 := by
    intro h; apply h3; rw [hsl]; simp only [Affine.addX]; linear_combination -h
  have hu0 : d / A2 ≠ 0 := div_ne_zero hd0 hA20
  have hℓd : ℓ * d = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
    rw [hℓ]; field_simp
  clear_value d ℓ A2
  refine ⟨⟨Units.mk0 (d / A2) hu0, x₀, ℓ, y₀⟩, -(A2 / (d / A2) ^ 2),
    1 - (W.a₁ + 2 * ℓ) / (d / A2), ?_, rfl, rfl⟩
  ext
  · simp only [variableChange_a₁, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    ring
  · simp only [variableChange_a₂, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hA2]; field_simp
  · simp only [variableChange_a₃, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [show W.a₃ + x₀ * W.a₁ + 2 * y₀ = d by rw [hd]; ring]; field_simp
  · simp only [variableChange_a₄, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_eq_zero]; right
    linear_combination -hℓd + ℓ * hd
  · simp only [variableChange_a₆, tateNF, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_eq_zero]; right
    linear_combination -heq

/-- The order hypotheses in terms of Mathlib's group of points. -/
theorem not_two_torsion [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0) :
    y₀ ≠ W.toAffine.negY x₀ y₀ := fun hy => h2P (Affine.Point.add_self_of_Y_eq hy)

theorem not_flex [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0)
    (h3P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) +
      (Affine.Point.some x₀ y₀ h) ≠ 0) :
    W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ y₀ y₀) ≠ x₀ := by
  intro hx
  have hy := not_two_torsion W h h2P
  set P := Affine.Point.some x₀ y₀ h
  have hPP := Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  rcases (Affine.Point.X_eq_iff (h₁ := Affine.nonsingular_add h h fun hxy => hy hxy.right)
    (h₂ := h)).1 hx with e | e
  · rw [← hPP] at e
    have : P = 0 := by
      simpa using congrArg (· - P) e
    exact Affine.Point.some_ne_zero h this
  · rw [← hPP] at e
    apply h3P; rw [e, neg_add_cancel]

/-- **Existence of the Tate normal form** for a point `P` with `2P ≠ 0`, `3P ≠ 0`. -/
theorem exists_tateNF [DecidableEq K] (W : WeierstrassCurve K) {x₀ y₀ : K}
    (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) ≠ 0)
    (h3P : (Affine.Point.some x₀ y₀ h) + (Affine.Point.some x₀ y₀ h) +
      (Affine.Point.some x₀ y₀ h) ≠ 0) :
    ∃ (C : VariableChange K) (b c : K), C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀ :=
  exists_tateNF_coord W x₀ y₀ h.1 (not_two_torsion W h h2P) (not_flex W h h2P h3P)

/-- **Uniqueness of the Tate normal form**: a change of variables fixing `(0, 0)` between two
Tate normal forms with `b ≠ 0` is the identity, and `(b, c) = (b', c')`. (`b ≠ 0` holds on
every elliptic `E(b, c)`: `b ∣ Δ(b, c)`.) -/
theorem tateNF_unique (b c b' c' : K) (hb : b ≠ 0) (C : VariableChange K)
    (hC : C • tateNF b c = tateNF b' c') (hr : C.r = 0) (ht : C.t = 0) :
    C = 1 ∧ b = b' ∧ c = c' := by
  have e1 := congrArg WeierstrassCurve.a₁ hC
  have e2 := congrArg WeierstrassCurve.a₂ hC
  have e3 := congrArg WeierstrassCurve.a₃ hC
  have e4 := congrArg WeierstrassCurve.a₄ hC
  simp only [variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, tateNF, hr, ht,
    Units.val_inv_eq_inv_val] at e1 e2 e3 e4
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    have : C.s * b = 0 := by
      have := e4; field_simp at this; linear_combination this
    exact (mul_eq_zero.1 this).resolve_right hb
  rw [hs] at e1 e2
  have hu1 : (C.u : K) = 1 := by
    have h23 : (C.u : K)⁻¹ ^ 2 * b = (C.u : K)⁻¹ ^ 3 * b := by
      linear_combination -e2 + e3
    field_simp at h23
    exact h23
  rw [hu1] at e1 e2
  refine ⟨?_, by linear_combination -e2, by linear_combination -e1⟩
  have hU : C.u = 1 := Units.val_eq_one.1 hu1
  rcases C with ⟨u, r, s, t⟩
  simp only at hr ht hs hU
  subst hr ht hs hU
  rfl

end BPModCurves

#print axioms BPModCurves.exists_tateNF
#print axioms BPModCurves.tateNF_unique
