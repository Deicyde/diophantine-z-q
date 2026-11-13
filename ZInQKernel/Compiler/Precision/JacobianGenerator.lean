import ZInQKernel.Compiler.Precision.Jacobian
import ZInQKernel.Model.Field.Curve

/-!
# The fixed Jacobian point

Blueprint: `compiler/natural/precision/jacobian-generator.md`.

In `ℤ[s]`, with `A = -11243 + 7950 s`, the triple `(X₀, Y₀, Z₀) = (3282 - 2320 s,
-247440 + 174966 s, 4)` satisfies `Y₀² = X₀³ + A X₀ Z₀⁴` (both sides are
`122452755912 - 86587174080 s`), and `(X₀/Z₀², Y₀/Z₀³) = (x(P₀), y(P₀))` in `K₀`. This is a finite
computation on explicit integers, independent of the generator theorem.
-/

namespace ZInQ.Compiler.Precision

open JTriple WeierstrassCurve WeierstrassCurve.Affine

/-- `A = -d² = -11243 + 7950 s` in `ℤ[s]`. -/
def Acoef : Zs := ⟨-11243, 7950⟩

/-- The fixed Jacobian point `P₀ᴶ = (3282 - 2320 s, -247440 + 174966 s, 4)`. -/
def P0J : JTriple Zs := ⟨⟨3282, -2320⟩, ⟨-247440, 174966⟩, ⟨4, 0⟩⟩

theorem P0J_Y_sq : P0J.Y ^ 2 = ⟨122452755912, -86587174080⟩ := by
  ext <;> simp [P0J, pow_succ]

theorem P0J_rhs : P0J.X ^ 3 + Acoef * P0J.X * P0J.Z ^ 4 = ⟨122452755912, -86587174080⟩ := by
  ext <;> simp [P0J, Acoef, pow_succ]

/-- `Y₀² = X₀³ + A X₀ Z₀⁴`. -/
theorem curveE_P0J : curveE Acoef P0J = 0 := by
  rw [curveE, sub_sub, P0J_Y_sq, ← P0J_rhs, sub_self]

theorem toK0_Acoef : Zs.toK0 Acoef = -genD ^ 2 := by
  rw [neg_genD_sq]; ext <;> simp [Acoef]

/-- `X₀/Z₀² = x(P₀)` and `Y₀/Z₀³ = y(P₀)`. -/
theorem P0J_affine :
    Zs.toK0 P0J.X / Zs.toK0 P0J.Z ^ 2 = genX0 ∧ Zs.toK0 P0J.Y / Zs.toK0 P0J.Z ^ 3 = genY0 := by
  have hZ : Zs.toK0 P0J.Z = 4 := by ext <;> simp [P0J]
  rw [hZ]
  constructor
  · rw [div_eq_iff (by norm_num)]; ext <;> simp [P0J, genX0] <;> norm_num
  · rw [div_eq_iff (by norm_num)]; ext <;> simp [P0J, genY0, pow_succ] <;> norm_num

/-- The fixed projective point represents `P₀`. -/
theorem rep_P0J : Rep (-genD ^ 2) (P0J.map Zs.toK0) genP0 := by
  have hZ : (P0J.map Zs.toK0).Z ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp [P0J] at this
  refine Or.inr ⟨hZ, ?_⟩
  obtain ⟨h1, h2⟩ := P0J_affine
  exact (some_eq_some_of _ h1.symm h2.symm :)

end ZInQ.Compiler.Precision
