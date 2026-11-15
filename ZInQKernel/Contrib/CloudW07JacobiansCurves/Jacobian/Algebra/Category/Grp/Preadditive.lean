-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Category.Grp.Preadditive), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Pointwise finite sums of morphisms of abelian groups.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory

/-- A finite sum of morphisms of abelian groups is computed pointwise. -/
lemma AddCommGrpCat.sum_apply {moduleSheaf exponent : AddCommGrpCat} {indexType : Type*} (morphism : indexType → (moduleSheaf ⟶ exponent))
    (sectionValue : Finset indexType) (element : moduleSheaf) : (∑ index ∈ sectionValue, morphism index) element = ∑ index ∈ sectionValue, morphism index element := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv morphism sectionValue) element)
