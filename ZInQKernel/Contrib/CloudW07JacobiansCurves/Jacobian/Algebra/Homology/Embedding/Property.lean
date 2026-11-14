-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Homology.Embedding.Property), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Properties of terms of extended complexes

Properties containing zero and stable under isomorphisms pass termwise to an extended complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- If `P` contains zero objects and is closed under isomorphisms and all terms of `K` satisfy
`P`, then all terms of `K.extend e` satisfy `P`. -/
lemma prop_extend_X (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {K : HomologicalComplex C c} (e : c.Embedding c') (hK : ∀ i, P (K.X i)) (i' : ι') :
    P ((K.extend e).X i') := by
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    exact P.prop_of_iso (K.extendXIso e hi).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_extend_X e i' (by simpa using h))

end HomologicalComplex
