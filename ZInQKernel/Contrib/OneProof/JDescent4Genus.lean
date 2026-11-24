import ZInQKernel.Contrib.OneProof.JDescent4Degree
import ZInQKernel.Contrib.OneProof.JDescent4Places
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz

/-! Hurwitz applied to the étale self-isogeny of the dimension-one abelian variety. -/

namespace HDec.CMBranch.CMjBridges

noncomputable section

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- Tau Ceti's genus of the actual function field of a dimension-one abelian variety is one. -/
theorem abVarFunctionFieldGenusOne : AbVarFunctionFieldGenusOne := by
  intro K _ _ A hdim
  let F := AbVarFunctionField A
  let f := abVarDouble A
  change TauCeti.genus K F = 1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let alg : Algebra F F := f.functionFieldMap.hom.toAlgebra
  let : Algebra F F := alg
  let : SMul F F := alg.toSMul
  let : Module F F := @Algebra.toModule F F _ _ alg
  let : IsScalarTower K F F := abVar_functionFieldMap_isScalarTower A A f (abVarDouble_over A)
  have hd := abVarDouble_functionField_degree A hdim
  let : Module.Finite F F := hd.1
  have hF : TauCeti.IsFunctionField K F := abVar_isFunctionField A hdim
  have hc : IsIntegrallyClosedIn K F := abVar_exactConstants A hdim
  have hram := abVar_ramificationIdx_eq_one_of_finite_unramified A A hdim hdim f (abVarDouble_over A)
  have hdiff : TauCeti.Divisor.different K F hF = 0 :=
    (TauCeti.Divisor.different_eq_zero_iff K F hF).2 fun P => by
      have h := (P.ramificationIdx_eq_differentExponent_add_one_iff K F).2
        (P.isTame_of_charZero K F)
      rw [hram P] at h
      omega
  have h := TauCeti.hurwitz_genus_formula (k := K) (k' := K) hF hF hc hc
  have hfour : Module.finrank F F = 4 := hd.2
  rw [Module.finrank_self, Nat.cast_one, one_mul, hfour, hdiff, map_zero, mul_zero, add_zero] at h
  omega

/-- The positive pole-space dimension ladder at the actual identity place, including
functions of exact pole orders two and three. -/
theorem abVar_identityPoleSpaces {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (hdim : A.dim = 1) :
    ∃ P : TauCeti.Place K (AbVarFunctionField A), P.degree = 1 ∧
      (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
        (AbVarFunctionField A)).range = P.integers.toSubring ∧
      (∀ n : ℕ, 1 ≤ n →
        TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) :
          TauCeti.Divisor K (AbVarFunctionField A)) = n) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ x : AbVarFunctionField A,
        x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q, Q ≠ P → 0 ≤ Q.ord x) :=
  abVar_identityPoleSpaces_of_genusOne abVarFunctionFieldGenusOne A hdim

#print axioms abVarFunctionFieldGenusOne
#print axioms abVar_identityPoleSpaces

end

end HDec.CMBranch.CMjBridges
