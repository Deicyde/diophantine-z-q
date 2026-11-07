import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.Multiplication.Certificate.Tests
import ZInQKernel.Hypotheses.Pole

/-!
# The slope predicate

Blueprint: `multiplication/certificate/slope-predicate.md`.

`SlopePred t ℓ c` is `Slope(t, ℓ; c)`: `t ∉ 𝒞 ∪ {1}`, `ℓ ≠ 0`, and there are a sign `η`, a
rational `q` and six test groups `(h_g, z_g)` such that, with `R₀ = ηF(t)/(t - 1)⁸`,
`a = 1 - R₀q²`, `R = ℓ²a²R₀`, the normalized tests
`C_{gj} = τ_j(h_g, z_g; c) / (R₀^{k_j} (t - 1)^{k_j + 1})`, `W_g = ∏_j (1 + R C_{gj}²)` and
`Θ = Tr Σ_g W_g⁻¹ = 2 Re Σ_g W_g⁻¹` (`QuadraticAlgebra.trace`), one has `a ≠ 0`,
`h_g ≠ 0`, `h_g ≠ c₀`, `W_g ≠ 0`, `Θ ≠ 0` and `Φ(R/Θ²)`.

The intermediate quantities are named functions (`slopeR0`, `slopeA`, `slopeR`, `normTests`,
`groupW`, `traceTheta`) so that the predicate can be unfolded step by step. In the certificate
`ℓ = ℓ₀` and `c = certShifts n = (c_*, c_* n₁, c_* n₂, c_* n₃)`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- `R₀ = η F(t) / (t - 1)⁸`. -/
def slopeR0 (η t : ℚ) : ℚ := η * contactPoly t / (t - 1) ^ 8

/-- `a = 1 - R₀ q²`. -/
def slopeA (R0 q : ℚ) : ℚ := 1 - R0 * q ^ 2

/-- `R = ℓ² a² R₀`. -/
def slopeR (ℓ a R0 : ℚ) : ℚ := ℓ ^ 2 * a ^ 2 * R0

/-- The normalized tests `C_j = D_j / (R₀^{k_j} (t - 1)^{k_j + 1})`. -/
noncomputable def normTests (R0 t : ℚ) (D : Fin 12 → K0) (j : Fin 12) : K0 :=
  D j / ((R0 : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1))

/-- `W = ∏_{j} (1 + R C_j²)`. -/
noncomputable def groupW (R : ℚ) (C : Fin 12 → K0) : K0 := ∏ j, (1 + (R : K0) * C j ^ 2)

/-- `Θ = Tr Σ_g W_g⁻¹` (`Tr(u + vs) = 2u`, `traceTheta_eq`). -/
noncomputable def traceTheta (W : Fin 6 → K0) : ℚ := QuadraticAlgebra.trace (∑ g, (W g)⁻¹)

theorem trace_K0 (u : K0) : QuadraticAlgebra.trace u = 2 * u.re := by
  rw [QuadraticAlgebra.trace_def]; ring

theorem traceTheta_eq (W : Fin 6 → K0) : traceTheta W = 2 * (∑ g, (W g)⁻¹).re :=
  trace_K0 _

/-- **The slope predicate** `Slope(t, ℓ; c)`. The six groups are `(h g, z g)`. -/
def SlopePred (t ℓ : ℚ) (c : Fin 4 → ℤ) : Prop :=
  t ∉ contactSet ∧ t ≠ 1 ∧ ℓ ≠ 0 ∧
    ∃ (η q : ℚ) (h : Fin 6 → ℤ) (z : Fin 6 → Fin 3 → ℤ),
      (η = 1 ∨ η = -1) ∧ slopeA (slopeR0 η t) q ≠ 0 ∧ (∀ g, h g ≠ 0 ∧ h g ≠ c 0) ∧
      (∀ g, groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
          (normTests (slopeR0 η t) t (testValues (h g) (z g) c)) ≠ 0) ∧
      traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
          (normTests (slopeR0 η t) t (testValues (h g) (z g) c))) ≠ 0 ∧
      PoleSoluble (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) /
        traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
          (normTests (slopeR0 η t) t (testValues (h g) (z g) c))) ^ 2)

/-- The shift indices `(c_*, c_* n₁, c_* n₂, c_* n₃)` of the multiplication certificate. -/
noncomputable def certShifts (n : Fin 3 → ℤ) : Fin 4 → ℤ :=
  ![(Syntax.cstar : ℤ), Syntax.cstar * n 0, Syntax.cstar * n 1, Syntax.cstar * n 2]

/-- `R₀ ≠ 0` for `t ∉ 𝒞 ∪ {1}` and `η = ±1`. -/
theorem slopeR0_ne_zero {η t : ℚ} (hη : η = 1 ∨ η = -1) (ht : t ∉ contactSet) (ht1 : t ≠ 1) :
    slopeR0 η t ≠ 0 := by
  have hη0 : η ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
  have ht1' : (t - 1) ^ 8 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 ht1)
  exact div_ne_zero (mul_ne_zero hη0 (contactPoly_ne_zero ht)) ht1'

/-- The pole input `R/Θ²` of a slope is nonzero, so the prefactor `B` of `Q_pole` does not make
the pole constraint vacuous. -/
theorem SlopePred.poleInput_ne_zero {t ℓ : ℚ} {c : Fin 4 → ℤ} (hs : SlopePred t ℓ c) :
    ∃ (η q : ℚ) (h : Fin 6 → ℤ) (z : Fin 6 → Fin 3 → ℤ),
      slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) /
        traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
          (normTests (slopeR0 η t) t (testValues (h g) (z g) c))) ^ 2 ≠ 0 ∧
      PoleSoluble (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) /
        traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
          (normTests (slopeR0 η t) t (testValues (h g) (z g) c))) ^ 2) := by
  obtain ⟨ht, ht1, hℓ, η, q, h, z, hη, ha, -, -, hΘ, hΦ⟩ := hs
  refine ⟨η, q, h, z, div_ne_zero ?_ (pow_ne_zero _ hΘ), hΦ⟩
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hℓ) (pow_ne_zero _ ha))
    (slopeR0_ne_zero hη ht ht1)

end ZInQ.Mult
