import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Rational descent of Galois-fixed geometric points

The fixed elements of the rational algebraic closure are rational, by the
infinite Galois fixed-field theorem. A geometric point fixed by every
rational automorphism therefore has rational coordinates.

The point at infinity descends to infinity. For an affine point, its
nonsingularity is reflected through the injective rational field map.
The resulting rational point maps to the original geometric point, and
injectivity of the actual point map proves uniqueness.

Only fixed-point descent for the existing manuscript point group is
proved here. No rational division, Selmer group, rank or restricted
converse is asserted.
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent

open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients

private theorem qbar_isGalois : IsGalois ℚ Qbar :=
  IsAlgClosure.isGalois ℚ Qbar

/-- An element of the existing closure is rational exactly when every rational automorphism fixes it. -/
theorem qbar_fixed_iff_rational (x : Qbar) :
    (∀ sigma : GaloisGroup, sigma.toAlgHom x = x) ↔
      ∃ q : ℚ, algebraMap ℚ Qbar q = x := by
  letI : IsGalois ℚ Qbar := qbar_isGalois
  constructor
  · intro hfixed
    have hauto : ∀ sigma : Qbar ≃ₐ[ℚ] Qbar, sigma x = x := by
      intro sigma
      exact hfixed sigma
    exact (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := ℚ) (K := Qbar) x).mpr hauto
  · rintro ⟨q, rfl⟩ sigma
    exact sigma.toAlgHom.commutes q

/-- Every fixed geometric point is the image of an actual rational point under the rational field map. -/
theorem exists_rationalPoint_of_galoisFixed (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, geometricPointMap ell sigma P = P) :
    ∃ R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P := by
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some x y hxy =>
      have hcoords : ∀ sigma : GaloisGroup,
          sigma.toAlgHom x = x ∧ sigma.toAlgHom y = y := by
        intro sigma
        have h := hfixed sigma
        change WeierstrassCurve.Affine.Point.map
            (R := ℚ) (S := ℚ) (F := Qbar) (K := Qbar)
            (W' := (ZInQ.Manuscript.curve ell).toAffine) sigma.toAlgHom
            (WeierstrassCurve.Affine.Point.some x y hxy) =
          WeierstrassCurve.Affine.Point.some x y hxy at h
        rw [WeierstrassCurve.Affine.Point.map_some] at h
        exact WeierstrassCurve.Affine.Point.some.inj h
      obtain ⟨qx, hqx⟩ := (qbar_fixed_iff_rational x).mp (fun sigma => (hcoords sigma).1)
      obtain ⟨qy, hqy⟩ := (qbar_fixed_iff_rational y).mp (fun sigma => (hcoords sigma).2)
      have hR : (ZInQ.Manuscript.curve ell).toAffine.Nonsingular qx qy := by
        apply (WeierstrassCurve.Affine.map_nonsingular
          (W := (ZInQ.Manuscript.curve ell).toAffine)
          (f := algebraMap ℚ Qbar) (algebraMap ℚ Qbar).injective qx qy).mp
        change ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular
          (algebraMap ℚ Qbar qx) (algebraMap ℚ Qbar qy)
        rw [hqx, hqy]
        exact hxy
      refine ⟨WeierstrassCurve.Affine.Point.some qx qy hR, ?_⟩
      subst hqx
      subst hqy
      rfl

/-- The rational preimage of a fixed geometric point is unique for the same actual point map. -/
theorem existsUnique_rationalPoint_of_galoisFixed (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, geometricPointMap ell sigma P = P) :
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P := by
  obtain ⟨R, hR⟩ := exists_rationalPoint_of_galoisFixed ell P hfixed
  refine ⟨R, hR, ?_⟩
  intro S hS
  exact WeierstrassCurve.Affine.Point.map_injective
    (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
    (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar)
    (hS.trans hR.symm)

/-- The same unique descent holds for the existing canonical geometric Galois action. -/
theorem existsUnique_rationalPoint_of_fixed (ell : ℚ) (P : GeometricPoints ell)
    (hfixed : ∀ sigma : GaloisGroup, sigma • P = P) :
    ∃! R : (ZInQ.Manuscript.curve ell).toAffine.Point,
      WeierstrassCurve.Affine.Point.map
        (R := ℚ) (S := ℚ) (F := ℚ) (K := Qbar)
        (W' := (ZInQ.Manuscript.curve ell).toAffine) (Algebra.ofId ℚ Qbar) R = P := by
  apply existsUnique_rationalPoint_of_galoisFixed ell P
  intro sigma
  simpa only [geometric_galois_smul] using hfixed sigma

end ZInQ.Contrib.OneProof.ManuscriptPole.RationalPointDescent
