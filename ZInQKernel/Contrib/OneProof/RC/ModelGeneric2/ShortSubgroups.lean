import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.PairJ

/-! # Stabilizers and cyclic subgroups on the ordinary short chart -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open Affine

variable {k : Type*} [Field k] [CharZero k] [DecidableEq k] {N : ℕ}

private theorem changePoints_neg {E : WeierstrassCurve k} [E.IsShortNF]
    (v : VariableChange k) (hv : v • E = E) (hu : (v.u : k) = -1)
    (hr : v.r = 0) (hs : v.s = 0) (ht : v.t = 0) (P : E.toAffine.Point) :
    (changePoints E E v hv).symm P = -P := by
  change Point.addEquivVariableChange E v
    ((AddEquiv.cast (M := fun W : WeierstrassCurve k => W.toAffine.Point) hv.symm) P) = -P
  cases P with
  | zero =>
    rw [← Point.zero_def, AddEquiv.cast_apply, Point.cast_zero hv.symm, map_zero, neg_zero]
  | some x y h =>
    rw [AddEquiv.cast_apply, Point.cast_some hv.symm, Point.coe_addEquivVariableChange,
      Point.equivVariableChange_some, Point.neg_some]
    norm_num [hu, hr, hs, ht, Affine.negY, a₁_of_isShortNF, a₃_of_isShortNF]

/-- Away from the two exceptional j-values, a change of variables preserving a short
equation preserves each subgroup. Its map on points is either identity or negation. -/
theorem subgroupPair_injective_of_short (E : WeierstrassCurve k) [E.IsElliptic] [E.IsShortNF]
    (hj₀ : E.j ≠ 0) (hj₁ : E.j ≠ 1728) :
    Function.Injective (subgroupPair (N := N) E) := by
  intro C D h
  have he := congrArg Subtype.val h
  obtain ⟨v, hv, hvC⟩ := (pairClasses_eq_iff
    (⟨E, inferInstance, C⟩ : EnhancedCurve k N) ⟨E, inferInstance, D⟩).1 he
  change v • E = E at hv
  haveI : (v • E).IsShortNF := hv.symm ▸ (inferInstance : E.IsShortNF)
  obtain ⟨hr, hs, ht⟩ := short_change_parameters E v (by norm_num) (by norm_num)
  have hv' : (⟨(v.u⁻¹)⁻¹, 0, 0, 0⟩ : VariableChange k) = v := by
    cases v
    simp_all
  have hu : (↑(v.u⁻¹) : k) ^ 2 = 1 := by
    have := (short_stabilizer E (by norm_num) (by norm_num) v.u⁻¹).1 (by rwa [hv'])
    simpa [hj₀, hj₁] using this
  change (changePoints E E v hv).mapAddSubgroup C.val = D.val at hvC
  apply Subtype.ext
  rcases sq_eq_one_iff.mp hu with hpos | hneg
  · have hu₁ : v.u⁻¹ = 1 := Units.ext hpos
    have huu : v.u = 1 := by simpa using congrArg Inv.inv hu₁
    have hv₁ : v = 1 := by
      cases v
      simp_all [VariableChange.one_def]
    subst v
    rw [changePoints_one] at hvC
    simpa using hvC
  · have hu₁ : v.u⁻¹ = -1 := Units.ext (by simpa using hneg)
    have huu : (v.u : k) = -1 := by
      have hvu : v.u = -1 := by simpa using congrArg Inv.inv hu₁
      simpa [hvu]
    let e := changePoints E E v hv
    have he' (P : E.toAffine.Point) : e.symm P = -P :=
      changePoints_neg v hv huu hr hs ht P
    rw [← hvC]
    ext P
    change P ∈ C.val ↔ ∃ Q ∈ C.val, e Q = P
    constructor
    · intro hP
      exact ⟨e.symm P, by rw [he']; exact C.val.neg_mem hP, e.apply_symm_apply P⟩
    · rintro ⟨Q, hQ, rfl⟩
      have hneg : -(e Q) = Q := (he' (e Q)).symm.trans (e.symm_apply_apply Q)
      rw [← C.val.neg_mem_iff, hneg]
      exact hQ

/-- For an elliptic equation away from the two exceptional j-values, the cyclic subgroup on
the chosen equation is determined by its pair class. Change to short form to apply
the stabilizer computation. -/
theorem subgroupPair_injective (E : WeierstrassCurve k) [E.IsElliptic]
    (hj₀ : E.j ≠ 0) (hj₁ : E.j ≠ 1728) :
    Function.Injective (subgroupPair (N := N) E) := by
  letI := invertibleOfNonzero (by norm_num : (2 : k) ≠ 0)
  letI := invertibleOfNonzero (by norm_num : (3 : k) ≠ 0)
  let v := E.toShortNF
  let V := v • E
  let e := changePoints E V v rfl
  let F := cyclicSubgroupsEquiv e N
  have hj : V.j = E.j := variableChange_j E v
  have hclass (C : CyclicSubgroups E.toAffine.Point N) :
      (subgroupPair E C).val = (subgroupPair V (F C)).val :=
    (pairClasses_eq_iff ⟨E, inferInstance, C⟩ ⟨V, inferInstance, F C⟩).2 ⟨v, rfl, rfl⟩
  intro C D he
  apply F.injective
  apply subgroupPair_injective_of_short V (hj.trans_ne hj₀) (hj.trans_ne hj₁)
  exact Subtype.ext ((hclass C).symm.trans ((congrArg Subtype.val he).trans (hclass D)))

#print axioms changePoints_neg
#print axioms subgroupPair_injective_of_short
#print axioms subgroupPair_injective

end WeierstrassCurve.ModelLevels.ModelGeneric2
