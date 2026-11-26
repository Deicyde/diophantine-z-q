import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.GenericGalois
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.FiniteDescent
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.PairQuotientValue
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

/-! # Descent of the actual second j-coordinate -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- At a geometric point of the pinned generic j-fibre, compute the invariant of the
quotient by its actual kernel on `EjBar`. Each step of `cyclicQuotientJ` quotients by
the least-prime-order part of the remaining kernel using Vélu and transports the
remaining kernel. The last equation gives `c₄ ^ 3 / Δ`. -/
noncomputable def genericQuotientValue (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) : Kbar :=
  EjBar.cyclicQuotientJ (genericJSubgroups h₂ x).val N

/-- The geometric quotient value reads the quotient of the pinned pair class,
independently of the chosen representative equation. -/
theorem genericQuotientValue_pairClass (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    genericQuotientValue h₂ x =
      pairQuotientJ (rationalPoints h₂ (genericJPointsOnRational h₂ x).val) := by
  rw [← genericJSubgroups_pairClass, pairQuotientJ_mk]
  rfl

/-- The quotient-invariant tuple transforms by the Galois automorphism on values. -/
theorem genericQuotientValue_galois (σ : Kbar ≃ₐ[Qj] Kbar)
    (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    genericQuotientValue h₂ (σ.toAlgHom.comp x) = σ (genericQuotientValue h₂ x) := by
  rw [genericQuotientValue, genericJSubgroups_galois]
  exact cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed Ej σ.toAlgHom
    (genericJSubgroups h₂ x).val N

private theorem existsUnique_genericQuotientJ :
    ∃! z : Y0RationalGenericJ h₂,
      ∀ x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar, x z = genericQuotientValue h₂ x := by
  letI := Y0RationalGenericJ_finite h₂
  letI := Y0RationalGenericJ_reduced h₂
  letI : IsGalois Qj Kbar := IsGalois.mk
  exact finiteReduced_descent _ (genericQuotientValue_galois h₂)

/-- The actual `j(E/C)` element of the pinned generic algebra. At every geometric point
apply the iterated prime-kernel Vélu formulas to its cyclic pair, transporting the
remaining subgroup after each step, and take `c₄ ^ 3 / Δ` of the final quotient curve.
The Galois-equivariant tuple of these values descends to the named finite reduced
algebra over the first j-coordinate. -/
noncomputable def Y0RationalGenericQuotientJ : Y0RationalGenericJ h₂ :=
  (existsUnique_genericQuotientJ h₂).exists.choose

/-- Evaluation of the descended element recovers the invariant of the actual quotient. -/
theorem Y0RationalGenericQuotientJ_eval (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    x (Y0RationalGenericQuotientJ h₂) = genericQuotientValue h₂ x :=
  (existsUnique_genericQuotientJ h₂).exists.choose_spec x

#print axioms genericQuotientValue
#print axioms genericQuotientValue_pairClass
#print axioms genericQuotientValue_galois
#print axioms existsUnique_genericQuotientJ
#print axioms Y0RationalGenericQuotientJ
#print axioms Y0RationalGenericQuotientJ_eval

end WeierstrassCurve.ModelLevels.ModelGeneric2
