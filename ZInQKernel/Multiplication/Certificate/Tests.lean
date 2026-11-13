import ZInQKernel.Model.Field.Codes
import ZInQKernel.Multiplication.Local.LogCoefficients

/-!
# The twelve local tests

Blueprint: `multiplication/certificate/twelve-tests.md`.

For `Q ∈ E(K₀)`: `ρ(Q) = 1/x(Q)` (`invX`, with `ρ(O) = 0`), `z(Q) = -x(Q)/y(Q)` (`zOf`, with
`z(O) = 0`) and `Λ(Q) = L(z(Q))` (`Lam`), where `L = truncLog (d²)` is the truncated logarithm
of the template `log25`. For integers `h, z₁, z₂, z₃, c₀, …, c₃` the twelve test values are
`testValues h z c : Fin 12 → K₀` (indices from `0`: `τ_{j+1}` of the article is
`testValues h z c j`, and `z i`, `i : Fin 3`, is the article's `z_{i+1}`).

The definitions are total: Lean's `u / 0 = 0` and `0⁻¹ = 0` fix the junk values; that the
denominators `Λ(H)`, `Λ(V₀)` are nonzero when `h ≠ 0` and `h ≠ c₀` is
`ZInQ.Mult.log25_z_ne_zero`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- `ρ(Q) = 1/x(Q)`, with `ρ(O) = 0`. -/
noncomputable def invX : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x _ _ => x⁻¹

/-- The local parameter `z(Q) = -x(Q)/y(Q)`, with `z(O) = 0`. -/
noncomputable def zOf : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x y _ => -x / y

/-- `Λ(Q) = L(z(Q))` with the truncated logarithm `L = truncLog (d²)`. -/
noncomputable def Lam (Q : genCurve.toAffine.Point) : K0 := truncLog (genD ^ 2) (zOf Q)

/-- **The twelve local tests** `τ(h, z; c)`: with `H = [h]P₀`, `U_i = [z_i]P₀`,
`V₀ = [h - c₀]P₀`, `V_i = [z_i - c_i]P₀`, `A_i = Λ(U_i)/Λ(H)` and `B_i = Λ(V_i)/Λ(V₀)`, the
values `ρ(H), ρ(U_i), σρ(V₀), σρ(V_i), A_i - σB_i, A₁A₂ - A₃`. -/
noncomputable def testValues (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) : Fin 12 → K0 :=
  let H := h • genP0
  let U : Fin 3 → genCurve.toAffine.Point := fun i => z i • genP0
  let V0 := (h - c 0) • genP0
  let V : Fin 3 → genCurve.toAffine.Point := fun i => (z i - c i.succ) • genP0
  let A : Fin 3 → K0 := fun i => Lam (U i) / Lam H
  let B : Fin 3 → K0 := fun i => Lam (V i) / Lam V0
  ![invX H, invX (U 0), invX (U 1), invX (U 2),
    star (invX V0), star (invX (V 0)), star (invX (V 1)), star (invX (V 2)),
    A 0 - star (B 0), A 1 - star (B 1), A 2 - star (B 2), A 0 * A 1 - A 2]

@[simp] theorem invX_zero : invX 0 = 0 := rfl

@[simp] theorem invX_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    invX (.some x y h) = x⁻¹ := rfl

@[simp] theorem zOf_zero : zOf 0 = 0 := rfl

@[simp] theorem zOf_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    zOf (.some x y h) = -x / y := rfl

/-- `Λ(O) = L(0) = 0`. -/
@[simp] theorem Lam_zero : Lam 0 = 0 := by
  simp [Lam, truncLog]

/-- The twelve test values, one by one. -/
theorem testValues_eq (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) :
    testValues h z c = ![invX (h • genP0), invX (z 0 • genP0), invX (z 1 • genP0),
      invX (z 2 • genP0), star (invX ((h - c 0) • genP0)),
      star (invX ((z 0 - c 1) • genP0)), star (invX ((z 1 - c 2) • genP0)),
      star (invX ((z 2 - c 3) • genP0)),
      Lam (z 0 • genP0) / Lam (h • genP0) -
        star (Lam ((z 0 - c 1) • genP0) / Lam ((h - c 0) • genP0)),
      Lam (z 1 • genP0) / Lam (h • genP0) -
        star (Lam ((z 1 - c 2) • genP0) / Lam ((h - c 0) • genP0)),
      Lam (z 2 • genP0) / Lam (h • genP0) -
        star (Lam ((z 2 - c 3) • genP0) / Lam ((h - c 0) • genP0)),
      Lam (z 0 • genP0) / Lam (h • genP0) * (Lam (z 1 • genP0) / Lam (h • genP0)) -
        Lam (z 2 • genP0) / Lam (h • genP0)] := rfl

end ZInQ.Mult
