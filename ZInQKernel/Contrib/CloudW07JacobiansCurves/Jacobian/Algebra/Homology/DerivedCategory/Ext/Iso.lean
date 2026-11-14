-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Homology.DerivedCategory.Ext.Iso), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Isomorphisms in the first variable of Ext

Precomposition with an isomorphism induces an additive equivalence of Ext groups.
-/

noncomputable section

universe objectUniverse morphismUniverse extUniverse

namespace CategoryTheory.Abelian.Ext

variable {category : Type objectUniverse} [Category.{morphismUniverse} category]
  [Abelian category] [HasExt.{extUniverse} category]
  {source target : category}

/-- Precomposition with an isomorphism is an additive equivalence on Ext. -/
def precompAddEquiv (isomorphism : source ≅ target) (coefficient : category) (degree : ℕ) :
    Ext target coefficient degree ≃+ Ext source coefficient degree where
  __ := (Ext.mk₀ isomorphism.hom).precomp coefficient (zero_add degree)
  invFun := (Ext.mk₀ isomorphism.inv).precomp coefficient (zero_add degree)
  left_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Abelian.Ext
