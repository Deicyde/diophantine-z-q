import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! On an étale coordinate chart of a smooth curve, the differential
of the coordinate is a basis of the relative differentials. -/

noncomputable section

open scoped TensorProduct

namespace KaehlerDifferential

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [Algebra (MvPolynomial (Fin 1) k) B]
  [IsScalarTower k (MvPolynomial (Fin 1) k) B]
  [Algebra.FormallyEtale (MvPolynomial (Fin 1) k) B]

/-- The coordinate differential gives the canonical one-element basis in
an étale algebra over the polynomial ring in one variable. -/
def etaleCurveBasis : Module.Basis (Fin 1) B Ω[B⁄k] :=
  ((mvPolynomialBasis k (Fin 1)).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin 1) k) B)

theorem etaleCurveBasis_apply (i : Fin 1) :
    etaleCurveBasis (k := k) (B := B) i =
      D k B (algebraMap (MvPolynomial (Fin 1) k) B (MvPolynomial.X i)) := by
  change tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin 1) k) B
    (((mvPolynomialBasis k (Fin 1)).baseChange B) i) = _
  apply (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin 1) k) B).symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_apply, mvPolynomialBasis_apply,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

/-- A differential on such a chart is uniquely a scalar times the
differential of its coordinate. -/
theorem existsUnique_smul_D_of_etaleCurve (ω : Ω[B⁄k]) :
    ∃! a : B, a • D k B (algebraMap (MvPolynomial (Fin 1) k) B (MvPolynomial.X 0)) = ω := by
  let e := etaleCurveBasis (k := k) (B := B)
  have h : ∀ a : B, a • D k B (algebraMap (MvPolynomial (Fin 1) k) B (MvPolynomial.X 0)) = ω ↔
      a = e.repr ω 0 := by
    intro a
    rw [← etaleCurveBasis_apply (k := k) (B := B) 0, ← e.repr.injective.eq_iff]
    constructor
    · intro he
      simpa [e, Finsupp.single_apply] using congrArg (fun v => v 0) he
    · intro he
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa [e, Finsupp.single_apply] using he
  exact ⟨e.repr ω 0, (h _).mpr rfl, fun a ha => (h a).mp ha⟩

end KaehlerDifferential

#print axioms KaehlerDifferential.existsUnique_smul_D_of_etaleCurve
