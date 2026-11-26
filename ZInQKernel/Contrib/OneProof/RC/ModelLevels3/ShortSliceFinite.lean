import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderIdempotents
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Finiteness of the short discriminant-one slice over the j-line -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion
open scoped TensorProduct

variable {R : Type*} [CommRing R]

private theorem normalizedShortPresentation_surjective {T : Type*} [CommRing T] [Algebra R T]
    (f : ShortBase R →ₐ[R] T) (hf : Function.Surjective f) (hδ : f (shortFamily R).Δ = 1) :
    Function.Surjective (f.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) (ShortBase R))) := by
  intro t
  obtain ⟨z, rfl⟩ := hf t
  obtain ⟨p, d, hp⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (shortEquation R).Δ) z
  have he := IsLocalization.mk'_spec (ShortBase R) p d
  rw [hp] at he
  have hd : f (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R) d) = 1 := by
    obtain ⟨m, hm⟩ := d.property
    rw [← hm, map_pow, map_pow]
    rw [← WeierstrassCurve.map_Δ]
    change (f (shortFamily R).Δ) ^ m = 1
    rw [hδ, one_pow]
  refine ⟨p, ?_⟩
  have h := congrArg f he
  change f (_ * _) = f _ at h
  rw [map_mul, hd, mul_one] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- On the short discriminant-one slice, the cube of the fourth coefficient
and the square of the sixth coefficient reduce to polynomials in the
actual short-family j-invariant. Hence this slice is finite over the j-line. -/
theorem shortDiscriminantSlice_finite {T : Type*} [CommRing T] [Algebra R T]
    (h6 : IsUnit (6 : R)) (f : ShortBase R →ₐ[R] T) (hf : Function.Surjective f)
    (hδ : f (shortFamily R).Δ = 1) :
    letI : Algebra (Polynomial R) T := (Polynomial.aeval (f (shortFamily R).j)
      : Polynomial R →ₐ[R] T).toRingHom.toAlgebra
    Module.Finite (Polynomial R) T := by
  let W := shortFamily R
  let : W.IsShortNF := shortFamily_IsShortNF
  let J := Polynomial R
  let jT : J →ₐ[R] T := Polynomial.aeval (f W.j)
  letI : Algebra J T := jT.toRingHom.toAlgebra
  let : IsScalarTower R J T := IsScalarTower.of_algebraMap_eq fun r => (jT.commutes r).symm
  let φ := f.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) (ShortBase R))
  let x := f W.a₄
  let y := f W.a₆
  have hC (r : R) : _root_.IsIntegral J (algebraMap R T r) := by
    rw [IsScalarTower.algebraMap_apply R J T]
    exact isIntegral_algebraMap
  have hc : IsUnit ((-48 : R) ^ 3) :=
    (isUnit_of_dvd_unit (show (-48 : R) ∣ (6 : R) ^ 4 from ⟨-27, by norm_num⟩) (h6.pow 4)).pow 3
  have hb : IsUnit (-432 : R) :=
    isUnit_of_dvd_unit ⟨-3, by norm_num⟩ (h6.pow 4)
  have hδinv : f (↑W.Δ'⁻¹ : ShortBase R) = 1 := by
    have h := congrArg f W.Δ'.inv_mul
    change f (_ * W.Δ) = f 1 at h
    have hδ' : f W.Δ = 1 := hδ
    rwa [map_mul, hδ', mul_one, map_one] at h
  have hj : algebraMap J T Polynomial.X = algebraMap R T ((-48 : R) ^ 3) * x ^ 3 := by
    change jT Polynomial.X = _
    rw [show jT Polynomial.X = f W.j from Polynomial.aeval_X _, WeierstrassCurve.j,
      W.c₄_of_isShortNF, map_mul, hδinv, one_mul, mul_pow, map_mul, map_pow, map_pow]
    norm_num [x, map_ofNat]
  have hx3 : x ^ 3 = algebraMap R T (↑hc.unit⁻¹ : R) * algebraMap J T Polynomial.X := by
    rw [hj, ← mul_assoc, ← map_mul, hc.val_inv_mul, map_one, one_mul]
  have hΔ : algebraMap R T (-64) * x ^ 3 + algebraMap R T (-432) * y ^ 2 = 1 := by
    calc
      _ = f W.Δ := by
        rw [W.Δ_of_isShortNF]
        simp only [map_mul, map_add, map_pow, map_neg, map_ofNat, x, y]
        ring
      _ = 1 := hδ
  have hy2 : y ^ 2 = algebraMap R T (↑hb.unit⁻¹ : R) *
      (1 - algebraMap R T (-64) * x ^ 3) := by
    rw [← hΔ, add_sub_cancel_left, ← mul_assoc, ← map_mul, hb.val_inv_mul, map_one, one_mul]
  have hx' : _root_.IsIntegral J (x ^ 3) := by
    rw [hx3]
    exact (hC _).mul isIntegral_algebraMap
  have hy' : _root_.IsIntegral J (y ^ 2) := by
    rw [hy2]
    exact (hC _).mul (isIntegral_one.sub ((hC _).mul hx'))
  have hX (i : Fin 2) : _root_.IsIntegral J (φ (MvPolynomial.X i)) := by
    fin_cases i
    · exact _root_.IsIntegral.of_pow (by decide : 0 < 3) hx'
    · exact _root_.IsIntegral.of_pow (by decide : 0 < 2) hy'
  let : Algebra.IsIntegral J T := by
    constructor
    intro t
    obtain ⟨p, rfl⟩ := normalizedShortPresentation_surjective f hf hδ t
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [show φ (MvPolynomial.C r) = algebraMap R T r from φ.commutes r]
      exact hC r
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      exact hp.mul (hX i)
  let : Algebra.FiniteType R T := Algebra.FiniteType.iff_quotient_mvPolynomial''.2
    ⟨2, φ, normalizedShortPresentation_surjective f hf hδ⟩
  let : Algebra.FiniteType J T := Algebra.FiniteType.of_restrictScalars_finiteType R J T
  exact Algebra.IsIntegral.finite

#print axioms normalizedShortPresentation_surjective
#print axioms shortDiscriminantSlice_finite

end WeierstrassCurve.ModelLevels
