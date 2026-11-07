import ZInQKernel.Compiler.Precision
import ZInQKernel.Hypotheses.Pole

/-!
# The six local tests

Blueprint: `assembly/value-templates/six-local-tests.md`.

For `n, κ ∈ ℤ` and `t ∈ ℚ`, `Test n κ t` holds when `κ ≠ 0`, `t ∉ 𝒞`, and there are integers
`h, s₀` and rationals `η, q` with `h ≠ 0`, `h ≠ κ`, `η² = 1`, `a₀ ≠ 0`, `W ≠ 0`,
`Θ = Tr(W⁻¹) ≠ 0` and `Φ(R/Θ²)`, where, with `H = [h]P₀`, `U = [s₀]P₀`, `V₀ = [h-κ]P₀`,
`V₁ = [s₀-κn]P₀`, `z = -x/y`, `w = 1/x` (both `0` at `O`) and `σ` the conjugation of `K₀`,
`D = (w(H), w(U), σ w(V₀), σ w(V₁), z(U)/z(H) - t, σ(z(V₁)/z(V₀)) - t)`,
`R₀ = η·2730⁶·F(t)`, `a₀ = 1 - R₀q²`, `R = R₀a₀²` and `W = ∏ⱼ (1 + R (Dⱼ/F(t))²)`.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Compiler.Precision

/-- The inverse abscissa `w(P) = 1/x` of an affine point; `w(O) = 0`. -/
noncomputable def wPt : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x _ _ => 1 / x

@[simp] theorem wPt_zero : wPt 0 = 0 := rfl

@[simp] theorem wPt_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    wPt (.some x y h) = 1 / x := rfl

/-- The contact polynomial `F(t) = t(t+15)(t+20)(t+24)(t+30)(t+60)`. -/
def contactPoly (t : ℚ) : ℚ := t * (t + 15) * (t + 20) * (t + 24) * (t + 30) * (t + 60)

/-- `F(t) ≠ 0` exactly when `t ∉ 𝒞`. -/
theorem contactPoly_ne_zero_iff (t : ℚ) : contactPoly t ≠ 0 ↔ t ∉ contactSet := by
  unfold contactPoly contactSet
  simp only [ne_eq, mul_eq_zero, not_or, Finset.mem_insert, Finset.mem_singleton]
  have e : ∀ c : ℚ, t + c = 0 ↔ t = -c := fun c => by constructor <;> intro h <;> linarith
  rw [e 15, e 20, e 24, e 30, e 60]
  tauto

/-- `F(n) = sixF(n)` at integers. -/
theorem contactPoly_intCast (n : ℤ) : contactPoly n = sixF n := by
  simp [contactPoly, sixF]

/-- The six tests `D₁, …, D₆ ∈ K₀` of `(n, κ, t)` with auxiliary indices `h, s₀`. -/
noncomputable def testD (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) : Fin 6 → K0 :=
  ![wPt (h • genP0), wPt (s₀ • genP0), star (wPt ((h - κ) • genP0)),
    star (wPt ((s₀ - κ * n) • genP0)),
    zPt (s₀ • genP0) / zPt (h • genP0) - algebraMap ℚ K0 t,
    star (zPt ((s₀ - κ * n) • genP0) / zPt ((h - κ) • genP0)) - algebraMap ℚ K0 t]

/-- `R₀ = η · 2730⁶ · F(t)`. -/
def testR0 (t η : ℚ) : ℚ := η * 2730 ^ 6 * contactPoly t

/-- `a₀ = 1 - R₀ q²`. -/
def testA0 (t η q : ℚ) : ℚ := 1 - testR0 t η * q ^ 2

/-- `R = R₀ a₀²`. -/
def testR (t η q : ℚ) : ℚ := testR0 t η * testA0 t η q ^ 2

/-- `W = ∏ⱼ (1 + R Cⱼ²)` with `Cⱼ = Dⱼ / F(t)`. -/
noncomputable def testW (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (η q : ℚ) : K0 :=
  ∏ j : Fin 6, (1 + algebraMap ℚ K0 (testR t η q) *
    (testD n κ t h s₀ j / algebraMap ℚ K0 (contactPoly t)) ^ 2)

/-- `Θ = Tr(W⁻¹)`. -/
noncomputable def testTheta (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (η q : ℚ) : ℚ :=
  QuadraticAlgebra.trace (testW n κ t h s₀ η q)⁻¹

/-- **The six local tests** `Test(n, κ, t)`. -/
def Test (n κ : ℤ) (t : ℚ) : Prop :=
  κ ≠ 0 ∧ t ∉ contactSet ∧ ∃ (h s₀ : ℤ) (η q : ℚ), h ≠ 0 ∧ h ≠ κ ∧ η ^ 2 = 1 ∧
    testA0 t η q ≠ 0 ∧ testW n κ t h s₀ η q ≠ 0 ∧ testTheta n κ t h s₀ η q ≠ 0 ∧
    PoleSoluble (testR t η q / testTheta n κ t h s₀ η q ^ 2)

/-- `2730⁶ = 413976684737889000000`. -/
theorem pow_six_2730_rat : (2730 : ℚ) ^ 6 = 413976684737889000000 := by norm_num

end ZInQ.Assembly
