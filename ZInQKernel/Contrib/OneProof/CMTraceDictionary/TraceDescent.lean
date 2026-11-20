import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-! Descent of the unaveraged point trace. The input is a point over the
extension field; no modularity, CM rationality, or conjugation sign is used. -/

namespace ZInQ.Manuscript.CMTraceDictionary

open scoped BigOperators
open WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
  [Algebra K L] [IsScalarTower ℚ K L]

open Classical in
/-- The sum of the Galois conjugates of an actual point is the base change of
a unique point, including when the sum is the point at infinity. -/
theorem existsUnique_point_of_sum_conjugates [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
    [DecidableEq K] [DecidableEq L]
    (E : WeierstrassCurve ℚ) (y : (E.baseChange L).toAffine.Point) :
    ∃! P : (E.baseChange K).toAffine.Point,
      Affine.Point.map (W' := E.toAffine) (IsScalarTower.toAlgHom ℚ K L) P =
        ∑ τ : L ≃ₐ[K] L, Affine.Point.map (W' := E.toAffine) (τ.toAlgHom.restrictScalars ℚ) y := by
  let act (τ : L ≃ₐ[K] L) :=
    Affine.Point.map (W' := E.toAffine) (τ.toAlgHom.restrictScalars ℚ)
  let s := ∑ τ : L ≃ₐ[K] L, act τ y
  change ∃! P, Affine.Point.map (W' := E.toAffine) (IsScalarTower.toAlgHom ℚ K L) P = s
  have fixed (σ : L ≃ₐ[K] L) : act σ s = s := by
    dsimp only [s]
    rw [map_sum]
    calc
      _ = ∑ τ : L ≃ₐ[K] L, act (σ * τ) y := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        exact Affine.Point.map_map (τ.toAlgHom.restrictScalars ℚ)
          (σ.toAlgHom.restrictScalars ℚ) y
      _ = _ := Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => act τ y)
  have ex : ∃ P, Affine.Point.map (W' := E.toAffine) (IsScalarTower.toAlgHom ℚ K L) P = s := by
    rcases s with _ | ⟨x, z, h⟩
    · exact ⟨0, Affine.Point.map_zero _⟩
    · have inv (σ : L ≃ₐ[K] L) : σ x = x ∧ σ z = z := by
        change (σ.toAlgHom.restrictScalars ℚ) x = x ∧ (σ.toAlgHom.restrictScalars ℚ) z = z
        simpa only [act, Affine.Point.map_some, Affine.Point.some.injEq] using fixed σ
      obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ => (inv σ).1
      obtain ⟨z₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed z).mpr fun σ => (inv σ).2
      let a := IsScalarTower.toAlgHom ℚ K L
      have h' : (E.baseChange K).toAffine.Nonsingular x₀ z₀ :=
        (Affine.baseChange_nonsingular E.toAffine (f := a) a.injective x₀ z₀).mp h
      exact ⟨.some x₀ z₀ h', Affine.Point.map_some a h'⟩
  obtain ⟨P, hP⟩ := ex
  exact ⟨P, hP, fun Q hQ => Affine.Point.map_injective _ (hQ.trans hP.symm)⟩

end ZInQ.Manuscript.CMTraceDictionary
