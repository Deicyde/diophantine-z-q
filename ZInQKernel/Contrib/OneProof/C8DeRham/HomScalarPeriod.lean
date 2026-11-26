import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The scalar period of an intertwining Hom line

An intertwiner fixed on its coefficients, read in two bases of periods, has
at least one nonzero coordinate. That coordinate is a period of the actual
character acting on the line. The computation works over any period field.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

section Matrix

variable {B ι G : Type*} [Field B] [Fintype ι] [DecidableEq ι] [Nonempty ι]

private def scalarPeriodUnit : Bˣ →* GL ι B :=
  Units.map (Matrix.scalar ι : B →+* Matrix ι ι B).toMonoidHom

private theorem scalarPeriodUnit_commute (b : Bˣ) (A : GL ι B) :
    Commute (scalarPeriodUnit b) A := by
  apply Units.ext
  change Matrix.scalar ι (b : B) * (A : Matrix ι ι B) =
    (A : Matrix ι ι B) * Matrix.scalar ι (b : B)
  exact Matrix.scalar_commute _ (fun r => Commute.all (b : B) r) _

/-- If `r T = χ T ρ`, with `T` fixed by the coefficient-field group, the
period matrix `Aᵣ T Aρ⁻¹` transforms by `χ`. Neither `χ` nor either original
matrix representation is specialized to a particular Hodge–Tate weight. -/
theorem exists_hom_scalar_period (a : G → B →+* B)
    (r ρ : G → GL ι B) (χ : G → Bˣ) (Aᵣ Aρ T : GL ι B)
    (hr : ∀ g, Matrix.GeneralLinearGroup.map (a g) Aᵣ = Aᵣ * r g)
    (hρ : ∀ g, Matrix.GeneralLinearGroup.map (a g) Aρ = Aρ * ρ g)
    (hfix : ∀ g, Matrix.GeneralLinearGroup.map (a g) T = T)
    (hT : ∀ g, r g * T = scalarPeriodUnit (χ g) * (T * ρ g)) :
    ∃ b : B, b ≠ 0 ∧ ∀ g, a g b = (χ g : B) * b := by
  let Q := Aᵣ * T * Aρ⁻¹
  have hQ : Q * Aρ = Aᵣ * T := by simp [Q, mul_assoc]
  have hper (g : G) : Matrix.GeneralLinearGroup.map (a g) Q = scalarPeriodUnit (χ g) * Q := by
    let f : GL ι B →* GL ι B := Matrix.GeneralLinearGroup.map (a g)
    have heρ : f Aρ = Aρ * ρ g := hρ g
    have her : f Aᵣ = Aᵣ * r g := hr g
    have hef : f T = T := hfix g
    change f Q = scalarPeriodUnit (χ g) * Q
    apply mul_right_cancel (b := Aρ * ρ g)
    calc
      f Q * (Aρ * ρ g) = f Q * f Aρ := congrArg (f Q * ·) heρ.symm
      _ = f (Q * Aρ) := (map_mul f Q Aρ).symm
      _ = (Aᵣ * r g) * T := by rw [hQ, map_mul, her, hef]
      _ = Aᵣ * (scalarPeriodUnit (χ g) * (T * ρ g)) := by rw [mul_assoc, hT g]
      _ = (Aᵣ * scalarPeriodUnit (χ g)) * (T * ρ g) := (mul_assoc _ _ _).symm
      _ = (scalarPeriodUnit (χ g) * Aᵣ) * (T * ρ g) := by
        rw [(scalarPeriodUnit_commute (χ g) Aᵣ).eq]
      _ = scalarPeriodUnit (χ g) * ((Q * Aρ) * ρ g) := by rw [hQ]; simp only [mul_assoc]
      _ = (scalarPeriodUnit (χ g) * Q) * (Aρ * ρ g) := by simp only [mul_assoc]
  let i : ι := Classical.choice inferInstance
  obtain ⟨j, hj⟩ : ∃ j, (Q : Matrix ι ι B) i j ≠ 0 := by
    by_contra! h
    exact Matrix.GeneralLinearGroup.det_ne_zero Q (Matrix.det_eq_zero_of_row_eq_zero i h)
  refine ⟨(Q : Matrix ι ι B) i j, hj, fun g => ?_⟩
  have h := congrArg (fun M : GL ι B => (M : Matrix ι ι B) i j) (hper g)
  rw [Matrix.GeneralLinearGroup.map_apply, Units.val_mul] at h
  change a g ((Q : Matrix ι ι B) i j) = (Matrix.scalar ι (χ g : B) * (Q : Matrix ι ι B)) i j at h
  rwa [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_apply, smul_eq_mul] at h

end Matrix
end HDec.G0Galois.C8Conrad.Manuscript
