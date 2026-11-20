import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Shapiro

/-!
# Weighted transfer on actual continuous cohomology

This is the map-level bridge used after choosing the coefficient embedding over the
upper field. The lower action can contain a quadratic twist (including its dyadic
part) and a deck quotient. The upper embedding is equivariant because both are
trivial on the upper subgroup. The resulting sum is the genuine corestriction.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppEK1

open CategoryTheory SelmerComplex

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} [U.FiniteIndex]
  {k : Type u} [CommRing k]
  {M P : Type u} [AddCommGroup M] [Module k M] [DistribMulAction U M]
  [SMulCommClass U k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul U M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

section Induced

variable (j : M →ₗ[k] ResMod (subgroupIncl U) P)
  (hj : ∀ (u : U) (m : M), j (u • m) = u • j m)

/-- Apply an equivariant coefficient embedding to the values of coinduced functions. -/
def inducedCoefficientMap :
    IndMod U k M →ₗ[k] IndMod U k (ResMod (subgroupIncl U) P) where
  toFun f := IndMod.mk (fun y => j (f y))
    (continuous_of_discreteTopology.comp f.continuous)
    (fun u y => by rw [IndMod.map_mul_left, hj])
  map_add' f g := by
    ext y
    exact j.map_add (f y) (g y)
  map_smul' a f := by
    ext y
    exact j.map_smul a (f y)

omit [U.FiniteIndex] [ContinuousSMul U M] [ContinuousSMul G P] in
/-- The equivariance of the induced map follows from right translation on its argument. -/
theorem inducedCoefficientMap_smul (g : G) (f : IndMod U k M) :
    inducedCoefficientMap j hj (g • f) = g • inducedCoefficientMap j hj f := by
  ext y
  rfl

variable (R : RightTransversal U) (hU : IsOpen (U : Set G))

/-- The coefficient embedding, applied to cochains over the upper subgroup. -/
abbrev upperCoefficientCochains :
    contCochains k U M ⟶ contCochains k U (ResMod (subgroupIncl U) P) :=
  contCochainsMap (ContinuousMonoidHom.id U) j continuous_of_discreteTopology hj

/-- The corresponding value-wise map on coinduced cochains. -/
abbrev inducedCoefficientCochains :
    contCochains k G (IndMod U k M) ⟶
      contCochains k G (IndMod U k (ResMod (subgroupIncl U) P)) :=
  contCochainsMap (ContinuousMonoidHom.id G) (inducedCoefficientMap j hj)
    continuous_of_discreteTopology (inducedCoefficientMap_smul j hj)

/-- Inverse Shapiro commutes with equivariant change of the upper coefficients.
This is equality of continuous cochain maps for the same transversal. -/
theorem shapiroInv_coefficient_natural :
    shapiroInv R hU k M ≫ inducedCoefficientCochains j hj =
      upperCoefficientCochains j hj ≫ shapiroInv R hU k (ResMod (subgroupIncl U) P) := by
  ext n c
  apply Subtype.ext
  funext g
  apply IndMod.ext
  intro y
  change j (asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el
      (((shapiroInv R hU k M).f n).hom c) : contCochain k G (IndMod U k M) n) g y) =
    asFun k G (IndMod U k (ResMod (subgroupIncl U) P))
      ((contSubCx k G (IndMod U k (ResMod (subgroupIncl U) P))).el
        (((shapiroInv R hU k (ResMod (subgroupIncl U) P)).f n).hom
          (((upperCoefficientCochains j hj).f n).hom c)) :
            contCochain k G (IndMod U k (ResMod (subgroupIncl U) P)) n) g y
  rw [shapiroInv_apply, shapiroInv_apply, hj]
  rfl

/-- On actual cochains, change upper coefficients and corestrict is exactly inverse
Shapiro followed by the value-wise coefficient map and the unnormalized norm. -/
theorem weightedTransfer_cochains :
    (shapiroInv R hU k M ≫ inducedCoefficientCochains j hj) ≫ normCochains R k P =
      upperCoefficientCochains j hj ≫ R.corCochains hU := by
  rw [shapiroInv_coefficient_natural j hj R hU, Category.assoc,
    ← corCochains_eq_shapiroInv_comp_norm R hU k P]

/-- The same identity on continuous `H¹`. This applies to a single level as well as
to a norm transition once its coefficient embedding has been identified. -/
theorem weightedTransfer_H1 :
    HomologicalComplex.homologyMap
        ((shapiroInv R hU k M ≫ inducedCoefficientCochains j hj) ≫ normCochains R k P) 1 =
      contCohomologyMap (ContinuousMonoidHom.id U) j continuous_of_discreteTopology hj 1 ≫
        R.corCohomology hU 1 := by
  rw [weightedTransfer_cochains j hj R hU]
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) 1).map_comp _ _

end Induced

end ZInQ.Manuscript.RC.AppEK1
