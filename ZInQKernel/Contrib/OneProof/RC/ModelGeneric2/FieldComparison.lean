import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientValue
import ZInQKernel.Contrib.OneProof.RC.X0Model.Rational
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_phiIrreducible_all
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi

/-! # The pinned generic field in the fixed Laurent-series realization -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric ModularCurve IntermediateField
open ZInQ.Manuscript.RC

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
set_option synthInstance.maxHeartbeats 50000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

attribute [local instance] X0Model.jAlgebra

private theorem modularField_j :
    algebraMap Qj (modularFunctionField N) RatFunc.X = ⟨jq, jq_mem N⟩ := by
  let i := Subfield.inclusion (show ℚ⟮jq⟯.toSubfield ≤ (modularFunctionField N).toSubfield
    from adjoin_jq_le N)
  change i (X0Model.jCoordinate RatFunc.X) = i jGen
  exact congrArg i X0Model.jCoordinate_X

private theorem genericModularPolynomial_map_jCoordinate (data : ModularPolynomialData N) :
    (genericModularPolynomial data).map X0Model.jCoordinate.toRingHom = data.toAdjoin := by
  rw [genericModularPolynomial, Polynomial.map_map, Polynomial.map_map,
    ModularPolynomialData.toAdjoin]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
    RatFunc.algebraMap_X, evalAtJGen, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]
  exact X0Model.jCoordinate_X

private theorem modularField_quotientJ_aeval (data : ModularPolynomialData N) :
    Polynomial.aeval (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)
      (genericModularPolynomial data) = 0 := by
  let inc : modularFunctionField N →+* LaurentSeries ℚ :=
    (modularFunctionField N).toSubfield.subtype
  apply inc.injective
  change inc
    ((genericModularPolynomial data).eval₂ (algebraMap Qj (modularFunctionField N))
      ⟨jqN N, jqN_mem N⟩) = 0
  rw [Polynomial.hom_eval₂ (genericModularPolynomial data)
    (algebraMap Qj (modularFunctionField N)) inc]
  have hcomp : inc.comp (algebraMap Qj (modularFunctionField N)) =
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)).comp X0Model.jCoordinate.toRingHom := rfl
  rw [hcomp, ← Polynomial.eval₂_map, genericModularPolynomial_map_jCoordinate,
    ← data.minpoly_jqN_eq (phiIrreducible_all N data)]
  exact minpoly.aeval (↥ℚ⟮jq⟯) (jqN N)

private theorem genericModularPolynomial_monic (data : ModularPolynomialData N) :
    (genericModularPolynomial data).Monic :=
  (data.monic.map _).map _

private theorem genericModularPolynomial_irreducible (data : ModularPolynomialData N) :
    Irreducible (genericModularPolynomial data) :=
  ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero ℚ N data
    (Nat.cast_ne_zero.mpr (NeZero.ne N))

private noncomputable def adjoinRootEquivOfDegree
    {B : Type} [CommRing B] [Nontrivial B] [Algebra Qj B] [FiniteDimensional Qj B]
    (data : ModularPolynomialData N) (x : B) (hx : Polynomial.aeval x (genericModularPolynomial data) = 0)
    (hdim : Module.finrank Qj B = dedekindPsi N) :
    {e : AdjoinRoot (genericModularPolynomial data) ≃ₐ[Qj] B //
      e (AdjoinRoot.root (genericModularPolynomial data)) = x} := by
  let p := genericModularPolynomial data
  letI : Fact (Irreducible p) := ⟨genericModularPolynomial_irreducible data⟩
  let b := AdjoinRoot.powerBasis' (genericModularPolynomial_monic data)
  letI : FiniteDimensional Qj (AdjoinRoot p) := b.finite
  have hdeg : Module.finrank Qj (AdjoinRoot p) = Module.finrank Qj B := by
    rw [b.finrank, hdim]
    change (genericModularPolynomial data).natDegree = dedekindPsi N
    rw [genericModularPolynomial, (data.monic.map _).natDegree_map, data.monic.natDegree_map,
      data.natDegree_eq]
  let f : AdjoinRoot p →ₐ[Qj] B := AdjoinRoot.liftAlgHom p (Algebra.ofId Qj B) x hx
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdeg (f := f.toLinearMap)).mp f.injective
  refine ⟨AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩, ?_⟩
  change f (AdjoinRoot.root p) = x
  exact AdjoinRoot.liftAlgHom_root p (Algebra.ofId Qj B) x hx

private theorem modularField_finrank : Module.finrank Qj (modularFunctionField N) = dedekindPsi N :=
  (Algebra.finrank_eq_of_equiv_equiv X0Model.jCoordinate (X0Model.secondCoordinate N) rfl).trans
    (finrank_adjoin_jqN_eq_dedekindPsi N)

private noncomputable def adjoinRootEquivGeneric (data : ModularPolynomialData N) :=
  letI := Y0RationalGenericJ_finite h₂
  letI : Nontrivial (Y0RationalGenericJ h₂) :=
    (genericJField h₂).toDivisionRing.toNontrivial
  adjoinRootEquivOfDegree data (Y0RationalGenericQuotientJ h₂)
    (genericQuotientJ_aeval h₂ data) (genericJFinrank h₂)

private noncomputable def adjoinRootEquivModular (data : ModularPolynomialData N) :=
  letI := X0Model.finite_jAlgebra N
  adjoinRootEquivOfDegree data (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)
    (modularField_quotientJ_aeval data) modularField_finrank

/-- The rational j-fibre has the fixed Laurent-series modular function field.
Its two distinguished elements are the source and quotient invariants. -/
noncomputable def genericModularFieldEquiv (data : ModularPolynomialData N) :
    Y0RationalGenericJ h₂ ≃ₐ[Qj] modularFunctionField N :=
  (adjoinRootEquivGeneric h₂ data).val.symm.trans (adjoinRootEquivModular data).val

/-- The first coordinate becomes the Laurent-series j-invariant. -/
theorem genericModularFieldEquiv_j (data : ModularPolynomialData N) :
    genericModularFieldEquiv h₂ data (algebraMap Qj (Y0RationalGenericJ h₂) RatFunc.X) =
      ⟨jq, jq_mem N⟩ := by
  rw [(genericModularFieldEquiv h₂ data).commutes, modularField_j]

/-- The actual Vélu quotient invariant becomes the specified Laurent series for j(Nτ). -/
theorem genericModularFieldEquiv_quotientJ (data : ModularPolynomialData N) :
    genericModularFieldEquiv h₂ data (Y0RationalGenericQuotientJ h₂) =
      ⟨jqN N, jqN_mem N⟩ := by
  rw [← (adjoinRootEquivGeneric h₂ data).property, genericModularFieldEquiv,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  exact (adjoinRootEquivModular data).property

#print axioms modularField_j
#print axioms genericModularPolynomial_map_jCoordinate
#print axioms modularField_quotientJ_aeval
#print axioms genericModularPolynomial_monic
#print axioms genericModularPolynomial_irreducible
#print axioms adjoinRootEquivOfDegree
#print axioms modularField_finrank
#print axioms adjoinRootEquivGeneric
#print axioms adjoinRootEquivModular
#print axioms genericModularFieldEquiv
#print axioms genericModularFieldEquiv_j
#print axioms genericModularFieldEquiv_quotientJ

end WeierstrassCurve.ModelLevels.ModelGeneric2
