import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AffineAlgebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Divisibility of the torsion abscissa equations -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion

/-- In an algebraically closed field, a root of the divisor-level abscissa equation
comes from a point killed by that level, hence by every multiple. Separability
makes the root inclusion sufficient for polynomial divisibility. -/
theorem xPolynomial_dvd_over_algClosed {k : Type*} [Field k] [IsAlgClosed k]
    (W : WeierstrassCurve k) [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : k))
    (hdN : d ∣ N) : xPolynomial W d ∣ xPolynomial W N := by
  classical
  have hd : IsUnit (d : k) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN
  have hs := separable_xPolynomial W hd.ne_zero
  have hne := (isUnit_leadingCoeff_xPolynomial W hN).ne_zero
  apply (IsAlgClosed.splits _).dvd_of_roots_le_roots hs.ne_zero
  apply (Multiset.le_iff_subset (Polynomial.nodup_roots hs)).2
  intro x hx
  have hx' := (mem_roots hs.ne_zero).mp hx
  obtain ⟨y, hP, ht⟩ := exists_torsion_ordinate W hx'
  apply (mem_roots (leadingCoeff_ne_zero.mp hne)).2
  apply (nsmul_some_eq_zero_iff W N hP).1
  obtain ⟨m, rfl⟩ := hdN
  rw [mul_nsmul, ht, nsmul_zero]

/-- Divisibility by a polynomial with unit leading coefficient descends along
an injective coefficient map by the monic division algorithm. -/
theorem dvd_of_map_dvd {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) {p r : A[X]}
    (hu : IsUnit p.leadingCoeff) (h : p.map f ∣ r.map f) : p ∣ r := by
  let q : A[X] := hu.unit⁻¹ • p
  have hq : q.Monic := monic_of_isUnit_leadingCoeff_inv_smul hu
  have heq : q = C (↑(hu.unit⁻¹) : A) * p := by
    change hu.unit⁻¹ • p = _
    rw [Units.smul_def, C_mul']
  have hunit : IsUnit (C (↑(hu.unit⁻¹) : A)) :=
    ((hu.unit⁻¹).isUnit).map C
  have hk' : q.map f ∣ r.map f := by
    rw [heq, Polynomial.map_mul]
    have hu' : IsUnit ((C (↑(hu.unit⁻¹) : A)).map f) :=
      hunit.map (Polynomial.mapRingHom f)
    exact hu'.mul_left_dvd.mpr h
  have ha := (map_dvd_map f hf hq).mp hk'
  rw [heq] at ha
  exact hunit.mul_left_dvd.mp ha

/-- Over a domain, test divisibility over an algebraic closure of its fraction
field and descend by division with a monic normalization of the divisor.
This applies in particular on the universal short locus at invertible level. -/
theorem xPolynomial_dvd {A : Type*} [CommRing A] [IsDomain A]
    (W : WeierstrassCurve A) [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : A))
    (hdN : d ∣ N) : xPolynomial W d ∣ xPolynomial W N := by
  let k := AlgebraicClosure (FractionRing A)
  let f : A →+* k := (algebraMap (FractionRing A) k).comp (algebraMap A (FractionRing A))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing A) k).injective.comp
      (IsFractionRing.injective A (FractionRing A))
  have hd : IsUnit (d : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN
  refine dvd_of_map_dvd f hf (isUnit_leadingCoeff_xPolynomial W hd) ?_
  rw [← map_xPolynomial, ← map_xPolynomial]
  exact xPolynomial_dvd_over_algClosed (W.map f) (by simpa using hN.map f) hdN

#print axioms xPolynomial_dvd_over_algClosed
#print axioms dvd_of_map_dvd
#print axioms xPolynomial_dvd

end WeierstrassCurve.ModelLevels
