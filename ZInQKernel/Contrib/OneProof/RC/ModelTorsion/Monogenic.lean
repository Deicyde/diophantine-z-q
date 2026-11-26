import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Norm.Defs

/-! # Étale monogenic algebras from a geometric root test -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial

universe u

variable {A : Type u} [CommRing A]

/-- In a polynomial quotient, a second polynomial is a unit if it vanishes
at none of the roots over any field receiving the coefficients. -/
theorem isUnit_mk_of_no_common_root (f g : A[X])
    (h : ∀ (K : Type u) [Field K] (i : A →+* K) (x : K),
      (f.map i).eval x = 0 → (g.map i).eval x ≠ 0) :
    IsUnit (AdjoinRoot.mk f g) := by
  by_contra hu
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  let : m.IsMaximal := hm
  let := Ideal.Quotient.field m
  let q := Ideal.Quotient.mk m
  let i := q.comp (AdjoinRoot.of f)
  let x := q (AdjoinRoot.root f)
  have h_eval (p : A[X]) : (p.map i).eval x = q (AdjoinRoot.mk f p) := by
    rw [eval_map, ← hom_eval₂]
    exact congrArg q (AdjoinRoot.aeval_eq (f := f) p)
  exact h (AdjoinRoot f ⧸ m) i x (by rw [h_eval, AdjoinRoot.mk_self, map_zero])
    ((h_eval g).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))

/-- Étaleness of the monic polynomial quotient with invertible derivative. -/
theorem etale_adjoinRoot_of_unit_derivative {f : A[X]} (hm : f.Monic)
    (hu : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale A (AdjoinRoot f) := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (g := f) (↑(hu.unit⁻¹) : AdjoinRoot f)
  have hd : f ∣ 1 - f.derivative * p := AdjoinRoot.mk_eq_zero.mp (by
    rw [map_sub, map_one, map_mul, hp]
    apply sub_eq_zero.mpr
    calc
      (1 : AdjoinRoot f) = ↑hu.unit * ↑(hu.unit⁻¹) := by simp
      _ = AdjoinRoot.mk f f.derivative * ↑(hu.unit⁻¹) :=
        congrArg (· * ↑(hu.unit⁻¹)) hu.unit_spec)
  obtain ⟨q, hq⟩ := hd
  let P : StandardEtalePair A :=
    ⟨f, hm, 1, ⟨p, q, 0, by rw [pow_zero, ← hq]; ring⟩⟩
  let r : AdjoinRoot f := AdjoinRoot.mk f (1 : A[X])
  let e : AdjoinRoot f ≃ₐ[AdjoinRoot f] Localization.Away r :=
    IsLocalization.atUnit (AdjoinRoot f) (Localization.Away r) r (by simp [r])
  have : Algebra.Etale A P.Ring := inferInstance
  exact Algebra.Etale.of_equiv
    (P.equivAwayAdjoinRoot.trans (e.symm.restrictScalars A))

/-- The discriminant of a polynomial with unit leading coefficient, expressed
as the signed norm of the derivative after monic normalization. -/
noncomputable def polynomialDiscriminant (f : A[X]) (h : IsUnit f.leadingCoeff) : A :=
  let m : A[X] := h.unit⁻¹ • f
  let d := f.natDegree
  f.leadingCoeff ^ (2 * d - 2) * (-1) ^ (d * (d - 1) / 2) *
    Algebra.norm A (AdjoinRoot.mk m m.derivative)

private theorem unit_derivative_of_separable_specializations (f : A[X])
    (h : ∀ (K : Type u) [Field K] (i : A →+* K), (f.map i).Separable) :
    IsUnit (AdjoinRoot.mk f f.derivative) := by
  apply isUnit_mk_of_no_common_root
  intro K _ i x hx
  rw [← derivative_map]
  exact (h K i).aeval_derivative_ne_zero (by simpa [aeval_def, Algebra.algebraMap_self] using hx)

private noncomputable def adjoinRootEquivMonic (f : A[X]) (h : IsUnit f.leadingCoeff) :
    AdjoinRoot f ≃ₐ[A] AdjoinRoot (h.unit⁻¹ • f) :=
  AdjoinRoot.algEquivOfAssociated A _ _
    ⟨Units.map C.toMonoidHom h.unit⁻¹, by simp [Units.smul_def, smul_eq_C_mul, mul_comm]⟩

/-- A polynomial with unit leading coefficient has the usual power basis. -/
noncomputable def basisAdjoinRoot (f : A[X]) (h : IsUnit f.leadingCoeff) :
    Module.Basis (Fin f.natDegree) A (AdjoinRoot f) := by
  let m : A[X] := h.unit⁻¹ • f
  have hd : m.natDegree = f.natDegree := natDegree_smul_of_smul_regular _ (IsSMulRegular.all _)
  exact ((AdjoinRoot.powerBasis' (monic_of_isUnit_leadingCoeff_inv_smul h)).basis.map
    (adjoinRootEquivMonic f h).symm.toLinearEquiv).reindex (finCongr hd)

/-- If the leading coefficient is a unit and every field specialization is
separable, the polynomial has unit discriminant and its quotient is finite
free and étale. -/
theorem monogenic_of_separable_specializations (f : A[X]) (h : IsUnit f.leadingCoeff)
    (hsep : ∀ (K : Type u) [Field K] (i : A →+* K), (f.map i).Separable) :
    IsUnit (polynomialDiscriminant f h) ∧ Module.Finite A (AdjoinRoot f) ∧
      Module.Free A (AdjoinRoot f) ∧ Algebra.Etale A (AdjoinRoot f) := by
  let m : A[X] := h.unit⁻¹ • f
  have hm : m.Monic := monic_of_isUnit_leadingCoeff_inv_smul h
  have hunit : IsUnit (C (↑h.unit⁻¹ : A)) := isUnit_C.mpr (Units.isUnit _)
  have hmul : m = f * C (↑h.unit⁻¹ : A) := by
    simp [m, Units.smul_def, smul_eq_C_mul, mul_comm]
  let e := adjoinRootEquivMonic f h
  have hd : IsUnit (AdjoinRoot.mk m m.derivative) := by
    apply unit_derivative_of_separable_specializations
    intro K _ i
    rw [hmul, Polynomial.map_mul]
    exact (hsep K i).mul_unit (hunit.map (Polynomial.mapRingHom i))
  have : Algebra.Etale A (AdjoinRoot m) := etale_adjoinRoot_of_unit_derivative hm hd
  exact ⟨((h.pow _).mul ((isUnit_one.neg).pow _)).mul (hd.map (Algebra.norm A)),
    Module.Finite.of_basis (basisAdjoinRoot f h),
    Module.Free.of_basis (basisAdjoinRoot f h), Algebra.Etale.of_equiv e.symm⟩

#print axioms isUnit_mk_of_no_common_root
#print axioms etale_adjoinRoot_of_unit_derivative
#print axioms unit_derivative_of_separable_specializations
#print axioms monogenic_of_separable_specializations

end WeierstrassCurve.ModelTorsion
