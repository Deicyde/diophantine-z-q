module

public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.FiniteGroup
public import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.Grading

/-! # Commuting finite-group invariants and degree zero -/

@[expose] public section

namespace RC.ModelInvariants

open DirectSum
open scoped TensorProduct

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S]
  (grading : ℤ → Submodule R S) [GradedAlgebra grading]

/-- Each group element preserves every homogeneous summand. -/
class PreservesGrading : Prop where
  smul_mem (g : G) {i : ℤ} {x : S} : x ∈ grading i → g • x ∈ grading i

variable [PreservesGrading (G := G) grading]

instance degreeZeroAction : MulSemiringAction G (degreeZero grading) where
  smul g x := ⟨g • (x : S), PreservesGrading.smul_mem (grading := grading) g x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : S))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : S))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : S) (y : S))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g x y := Subtype.ext (smul_mul' g (x : S) (y : S))

instance degreeZeroAction_comm : SMulCommClass G R (degreeZero grading) where
  smul_comm g r x := Subtype.ext (smul_comm g r (x : S))

/-- The homogeneous components in the invariant algebra are intersections with the ambient
homogeneous components. -/
def fixedGrading (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (n : ℤ) : Submodule R (FixedPoints.subalgebra R S G) :=
  (grading n).comap (FixedPoints.subalgebra R S G).val.toLinearMap

instance fixedGradingMonoid : SetLike.GradedMonoid (fixedGrading grading G) where
  one_mem := SetLike.one_mem_graded grading
  mul_mem _ _ _ _ hx hy := SetLike.mul_mem_graded (A := grading) hx hy

theorem fixedComponent (x : FixedPoints.subalgebra R S G) (i : ℤ) :
    (decompose grading (x : S) i : S) ∈ FixedPoints.subalgebra R S G := by
  intro g
  let f : grading →+*ᵍ grading :=
    { (MulSemiringAction.toAlgHom R S g).toRingHom with
      map_mem := PreservesGrading.smul_mem (grading := grading) g }
  have h := f.map_directSumDecompose (x := (x : S)) (i := i)
  change g • (decompose grading (x : S) i : S) =
    (decompose grading (g • (x : S)) i : S) at h
  rw [x.property g] at h
  exact h

/-- Grade-preserving group actions give the invariant algebra an internal grading. -/
noncomputable instance fixedGradedAlgebra : GradedAlgebra (fixedGrading grading G) := by
  classical
  let A := FixedPoints.subalgebra R S G
  let inc (i : ℤ) : fixedGrading grading G i →+ grading i :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have comm :
      A.val.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom (fixedGrading grading G)) =
        (DirectSum.coeAddMonoidHom grading).comp (DirectSum.map inc) := by
    apply DirectSum.addHom_ext
    intro i x
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, DirectSum.map_of]
    rfl
  apply DirectSum.IsInternal.gradedAlgebra
  constructor
  · intro x y h
    apply (DirectSum.map_injective inc).2 (fun i _ _ he =>
      Subtype.ext (Subtype.ext (congrArg (fun v : grading i => (v : S)) he)))
    apply (Decomposition.isInternal grading).injective
    exact (congrArg (fun f => f x) comm).symm.trans
      ((congrArg (fun v : A => (v : S)) h).trans (congrArg (fun f => f y) comm))
  · intro x
    let component (i : ℤ) : fixedGrading grading G i :=
      ⟨⟨decompose grading (x : S) i, fixedComponent grading x i⟩,
        (decompose grading (x : S) i).property⟩
    refine ⟨∑ i ∈ (decompose grading (x : S)).support, DirectSum.of _ i (component i), ?_⟩
    apply Subtype.ext
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    change A.val (∑ i ∈ (decompose grading (x : S)).support, (component i).val) = _
    rw [map_sum]
    exact sum_support_decompose grading (x : S)

/-- Taking degree zero and taking invariants commute. Both sides consist of elements that
belong to degree zero and are fixed by the group. -/
def fixedDegreeZeroEquiv :
    degreeZero (fixedGrading grading G) ≃ₐ[R]
      FixedPoints.subalgebra R (degreeZero grading) G where
  toFun x := ⟨⟨x.val.val, x.property⟩, fun g => Subtype.ext (x.val.property g)⟩
  invFun x := ⟨⟨x.val.val, fun g => congrArg Subtype.val (x.property g)⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (R' : Type*) [CommRing R'] [Algebra R R']

instance scalarExtensionPreservesGrading :
    PreservesGrading (G := G) (fun n => (grading n).baseChange R') where
  smul_mem g {i x} hx := by
    obtain ⟨y, hy⟩ := Submodule.toBaseChange_surjective' R' (grading i) hx
    rw [← hy]
    clear hy hx x
    induction y with
    | tmul a x =>
        change g • (a ⊗ₜ[R] (x : S)) ∈ (grading i).baseChange R'
        rw [scalarExtension_smul_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a
          (PreservesGrading.smul_mem (grading := grading) g x.property)
    | add x y hx hy =>
        rw [map_add, Submodule.coe_add, smul_add]
        exact add_mem hx hy

private theorem degreeZeroBaseChange_equivariant (g : G) (x : R' ⊗[R] degreeZero grading) :
    degreeZeroBaseChange grading R' (g • x) = g • degreeZeroBaseChange grading R' x := by
  induction x with
  | tmul a x =>
      apply Subtype.ext
      rw [scalarExtension_smul_tmul, degreeZeroBaseChange_tmul]
      change _ = g • (degreeZeroBaseChange grading R' (a ⊗ₜ[R] x) : R' ⊗[R] S)
      rw [degreeZeroBaseChange_tmul, scalarExtension_smul_tmul]
      rfl
  | add x y hx hy =>
      rw [smul_add g x y, map_add, hx, hy, map_add]
      exact (smul_add g _ _).symm

private noncomputable def fixedEquivOfEquivariant {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R' A] [Algebra R' B] [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G R' A] [SMulCommClass G R' B] (e : A ≃ₐ[R'] B)
    (he : ∀ g : G, ∀ x : A, e (g • x) = g • e x) :
    FixedPoints.subalgebra R' A G ≃ₐ[R'] FixedPoints.subalgebra R' B G :=
  AlgEquiv.ofBijective (e.toAlgHom.comp (FixedPoints.subalgebra R' A G).val |>.codRestrict _
    (fun x g => (he g x).symm.trans (congrArg e (x.property g))))
    ⟨fun _ _ eq => Subtype.ext (e.injective (congrArg Subtype.val eq)), fun y => by
      obtain ⟨x, hx⟩ := e.surjective y.val
      refine ⟨⟨x, fun g => e.injective ?_⟩, Subtype.ext hx⟩
      rw [he, hx, y.property g]⟩

/-- The two scalar-extension equivalences compose for the degree-zero invariant algebra. -/
@[no_expose] noncomputable def fixedDegreeZeroBaseChange [Fintype G] (h : IsUnit (Fintype.card G : R)) :
    (R' ⊗[R] degreeZero (fixedGrading grading G)) ≃ₐ[R']
      degreeZero (fixedGrading (fun n => (grading n).baseChange R') G) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R'] R')
      (fixedDegreeZeroEquiv grading)).trans <|
    (fixedPointsBaseChange (S := degreeZero grading) R' h).trans <|
    (fixedEquivOfEquivariant R' (degreeZeroBaseChange grading R')
      (degreeZeroBaseChange_equivariant grading R')).trans <|
    (fixedDegreeZeroEquiv (fun n => (grading n).baseChange R')).symm

#print axioms degreeZeroAction
#print axioms degreeZeroAction_comm
#print axioms fixedGrading
#print axioms fixedGradingMonoid
#print axioms fixedComponent
#print axioms fixedGradedAlgebra
#print axioms fixedDegreeZeroEquiv
#print axioms scalarExtensionPreservesGrading
#print axioms degreeZeroBaseChange_equivariant
#print axioms fixedEquivOfEquivariant
#print axioms fixedDegreeZeroBaseChange

end RC.ModelInvariants
