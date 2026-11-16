/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces

/-!
# Original FakeEC dimension and exact carrier/group data for D2

Original W01 dictionary glue, 2026-11-15, Metamate/agentcloud-assisted.
No geometric property is assumed except in the packaging-data identities,
where h is exactly the original constructor's explicit AbVarProps argument.
The dimension result applies to ANY such h and derives 2 from E.dim_fibre.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D2

open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj

/-- The unique field fibre is literally the whole underlying source space. -/
theorem fibre_eq_univ {K : Type} [Field K] (E : FakeEC K)
    (s : Spec (CommRingCat.of K)) : E.f.base ⁻¹' {s} = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

/-- The original fibre-dimension statement gives the dimension of E.A, not another model. -/
theorem source_dim_two {K : Type} [Field K] (E : FakeEC K) :
    topologicalKrullDim E.A = 2 := by
  have hf := E.dim_fibre (IsLocalRing.closedPoint K)
  rw [fibre_eq_univ E (IsLocalRing.closedPoint K)] at hf
  have hd : topologicalKrullDim (Set.univ : Set E.A) = topologicalKrullDim E.A :=
    IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ E.A)
      (Homeomorph.Set.univ E.A).isHomeomorph
  exact hd.symm.trans hf

/-- Exact constructor-data equality; no isomorphic or nominal substitute object. -/
theorem abVarOfFakeEC_data {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E) :
    abVarOfFakeEC E h =
      @PkgI3.AbVar.mk K _ (Over.mk E.f) E.L.grpObjOverMk h.1 h.2.1 h.2.2 := rfl

/-- Literal carrier equality. -/
theorem abVarOfFakeEC_X {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E) :
    (abVarOfFakeEC E h).X = Over.mk E.f := rfl

/-- The stored group structure is the given E.L's original Yoneda group object. -/
theorem abVarOfFakeEC_grp {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E) :
    HEq (abVarOfFakeEC E h).grp E.L.grpObjOverMk := HEq.rfl

/-- Dimension transport through the actual original packaging. -/
theorem abVarOfFakeEC_dim_two {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E) :
    (abVarOfFakeEC E h).dim = 2 := by
  change topologicalKrullDim E.A = 2
  exact source_dim_two E

#print axioms source_dim_two
#print axioms abVarOfFakeEC_data
#print axioms abVarOfFakeEC_dim_two

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D2
