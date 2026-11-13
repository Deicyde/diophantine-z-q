import ZInQKernel.Multiplication.Local
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Multiplication.Certificate.Constants

/-!
# The six local tests

Blueprint: `assembly/value-templates/six-local-tests.md` (defined here because the local-tests
lemmas need it first).

For `n, κ ∈ ℤ` and `t ∈ ℚ`, `Test n κ t` holds when `κ ≠ 0`, `t ∉ 𝒞`, and there are integers
`h, s₀` and rationals `η, q` with `h ≠ 0`, `h ≠ κ`, `η² = 1`, `a₀ ≠ 0`, `W ≠ 0`, `Θ ≠ 0` and
`Φ(R/Θ²)`, where `H = [h]P₀`, `U = [s₀]P₀`, `V₀ = [h - κ]P₀`, `V₁ = [s₀ - κ n]P₀`,

* `D₁ = w(H)`, `D₂ = w(U)`, `D₃ = σ(w(V₀))`, `D₄ = σ(w(V₁))`, `D₅ = z(U)/z(H) - t`,
  `D₆ = σ(z(V₁)/z(V₀)) - t` (`testD`), with `z = -x/y`, `w = 1/x`, `z(O) = w(O) = 0`;
* `R₀ = η · 2730⁶ · F(t)`, `a₀ = 1 - R₀ q²`, `R = R₀ a₀²` (`testR₀`, `testR`);
* `W = ∏ⱼ (1 + R Cⱼ²)` with `Cⱼ = Dⱼ / F(t)` (`poleW`), `Θ = Tr(W⁻¹)` (`poleTheta`).

`F(t) = t(t + 15)(t + 20)(t + 24)(t + 30)(t + 60)` is `Mult.contactPoly`.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult

theorem contactPoly_intCast (n : ℤ) :
    contactPoly n = (ZInQ.Compiler.Precision.sixF n : ℚ) := by
  simp [contactPoly, ZInQ.Compiler.Precision.sixF]

theorem contactPoly_ne_zero_iff {t : ℚ} : contactPoly t ≠ 0 ↔ t ∉ contactSet := by
  rw [contactPoly_eq_prod, Finset.prod_ne_zero_iff]
  constructor
  · intro h ht; exact h t ht (sub_self t)
  · intro ht c hc h0; rw [sub_eq_zero] at h0; subst h0; exact ht hc

/-- The six tests `D₁, …, D₆ ∈ K₀`. -/
noncomputable def testD (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) : Fin 6 → K0 :=
  ![wCoord (A := -genD ^ 2) (h • genP0), wCoord (A := -genD ^ 2) (s₀ • genP0),
    star (wCoord (A := -genD ^ 2) ((h - κ) • genP0)),
    star (wCoord (A := -genD ^ 2) ((s₀ - κ * n) • genP0)),
    Mult.zCoord (A := -genD ^ 2) (s₀ • genP0) / Mult.zCoord (A := -genD ^ 2) (h • genP0) - t,
    star (Mult.zCoord (A := -genD ^ 2) ((s₀ - κ * n) • genP0) /
      Mult.zCoord (A := -genD ^ 2) ((h - κ) • genP0)) - t]

/-- `R₀ = η · 2730⁶ · F(t)`. -/
def testR₀ (η t : ℚ) : ℚ := η * 2730 ^ 6 * contactPoly t

/-- `R = R₀ a₀²` with `a₀ = 1 - R₀ q²`. -/
def testR (η q t : ℚ) : ℚ := testR₀ η t * (1 - testR₀ η t * q ^ 2) ^ 2

/-- `W = ∏ⱼ (1 + R Cⱼ²)`. -/
noncomputable def poleW (R : ℚ) (C : Fin 6 → K0) : K0 := ∏ j, (1 + (R : K0) * C j ^ 2)

/-- `Θ = Tr(W⁻¹)`. -/
noncomputable def poleTheta (R : ℚ) (C : Fin 6 → K0) : ℚ :=
  QuadraticAlgebra.trace (poleW R C)⁻¹

/-- `Cⱼ = Dⱼ / F(t)`. -/
noncomputable def testC (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (j : Fin 6) : K0 :=
  testD n κ t h s₀ j / (contactPoly t : K0)

/-- **The six local tests** `Test(n, κ, t)`. -/
def Test (n κ : ℤ) (t : ℚ) : Prop :=
  κ ≠ 0 ∧ t ∉ contactSet ∧ ∃ (h s₀ : ℤ) (η q : ℚ), h ≠ 0 ∧ h ≠ κ ∧ η ^ 2 = 1 ∧
    1 - testR₀ η t * q ^ 2 ≠ 0 ∧ poleW (testR η q t) (testC n κ t h s₀) ≠ 0 ∧
    poleTheta (testR η q t) (testC n κ t h s₀) ≠ 0 ∧
    PoleSoluble (testR η q t / poleTheta (testR η q t) (testC n κ t h s₀) ^ 2)

end ZInQ.Assembly
