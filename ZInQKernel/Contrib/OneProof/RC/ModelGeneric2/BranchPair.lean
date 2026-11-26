import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.FieldComparison

/-! # The cyclic-pair reading at the generic point of the fixed branch -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric ModularCurve
open ZInQ.Manuscript.RC

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] X0Model.jAlgebra

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (data : ModularPolynomialData N)

private theorem genericPair_quotientJ (y : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    pairQuotientJ (genericJPairClasses h₂ y).val = y (Y0RationalGenericQuotientJ h₂) :=
  (genericQuotientValue_pairClass h₂ y).symm.trans (Y0RationalGenericQuotientJ_eval h₂ y).symm

private theorem branchPair_coordinates (x : modularFunctionField N →ₐ[Qj] Kbar) :
    let y := x.comp (genericModularFieldEquiv h₂ data).toAlgHom
    let c := (genericJPairClasses h₂ y).val
    pairJ c = x ⟨jq, jq_mem N⟩ ∧ pairQuotientJ c = x ⟨jqN N, jqN_mem N⟩ := by
  intro y c
  refine ⟨?_, (genericPair_quotientJ h₂ y).trans ?_⟩
  · rw [← genericModularFieldEquiv_j h₂ data]
    exact (genericJPairClasses h₂ y).property.trans (y.commutes RatFunc.X).symm
  · exact congrArg x (genericModularFieldEquiv_quotientJ h₂ data)

include h₂ data in
private theorem existsUnique_branchPair (x : modularFunctionField N →ₐ[Qj] Kbar) :
    ∃! c : PairClasses Kbar N,
      pairJ c = x ⟨jq, jq_mem N⟩ ∧ pairQuotientJ c = x ⟨jqN N, jqN_mem N⟩ := by
  let y := x.comp (genericModularFieldEquiv h₂ data).toAlgHom
  let e := genericJPairClasses h₂
  refine ⟨(e y).val, branchPair_coordinates h₂ data x, fun c hc => ?_⟩
  have hj : pairJ c = algebraMap Qj Kbar RatFunc.X := by
    rw [hc.1, ← genericModularFieldEquiv_j h₂ data]
    exact y.commutes RatFunc.X
  let c' : {t : PairClasses Kbar N // pairJ t = algebraMap Qj Kbar RatFunc.X} := ⟨c, hj⟩
  let z := e.symm c'
  have hz : (e z).val = c := congrArg Subtype.val (e.apply_symm_apply c')
  have heval : z (Y0RationalGenericQuotientJ h₂) = y (Y0RationalGenericQuotientJ h₂) := by
    rw [← genericPair_quotientJ h₂ z, ← genericPair_quotientJ h₂ y]
    change pairQuotientJ (e z).val = pairQuotientJ (e y).val
    rw [hz, hc.2]
    exact (branchPair_coordinates h₂ data x).2.symm
  have hzy : z = y := (genericQuotientValue_bijOn h₂ data).injOn
    (Set.mem_univ z) (Set.mem_univ y) <| by
      rw [← Y0RationalGenericQuotientJ_eval h₂ z, ← Y0RationalGenericQuotientJ_eval h₂ y]
      exact heval
  rw [← hz, hzy]

/-- Read the cyclic pair of a geometric point of the fixed Laurent-series
field by the actual invariants of the source and quotient curves. At the
generic j-coordinate these two invariant values specify one pair class. -/
noncomputable def modularFieldPairClass (x : modularFunctionField N →ₐ[Qj] Kbar) :
    PairClasses Kbar N :=
  (existsUnique_branchPair h₂ data x).exists.choose

theorem modularFieldPairClass_coordinates (x : modularFunctionField N →ₐ[Qj] Kbar) :
    pairJ (modularFieldPairClass h₂ data x) = x ⟨jq, jq_mem N⟩ ∧
      pairQuotientJ (modularFieldPairClass h₂ data x) = x ⟨jqN N, jqN_mem N⟩ :=
  (existsUnique_branchPair h₂ data x).exists.choose_spec

/-- The two actual readings agree on every geometric point over the generic j-line. -/
theorem modularFieldPairClass_eq_pinned (x : modularFunctionField N →ₐ[Qj] Kbar) :
    modularFieldPairClass h₂ data x =
      (genericJPairClasses h₂ (x.comp (genericModularFieldEquiv h₂ data).toAlgHom)).val :=
  (existsUnique_branchPair h₂ data x).unique (modularFieldPairClass_coordinates h₂ data x)
    (branchPair_coordinates h₂ data x)

#print axioms genericPair_quotientJ
#print axioms branchPair_coordinates
#print axioms existsUnique_branchPair
#print axioms modularFieldPairClass
#print axioms modularFieldPairClass_coordinates
#print axioms modularFieldPairClass_eq_pinned

end WeierstrassCurve.ModelLevels.ModelGeneric2
