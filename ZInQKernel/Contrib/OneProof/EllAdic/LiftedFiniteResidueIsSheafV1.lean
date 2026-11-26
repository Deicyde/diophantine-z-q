import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueDiagonalV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- The lifted locally constant finite residue presheaf is a sheaf. Use the
actual continuous-map sheaf with a discrete target and the same restriction
functor as `ellAdicSheaf`, without changing the finite transition maps. -/
theorem liftedFiniteResidueProEt_isSheaf (S : Scheme.{u}) (p n : ℕ) :
    Presheaf.IsSheaf (Scheme.ProEt.topology S) ((liftedFiniteResidueProEtTower S p).obj (op n)) := by
  let A := ULift.{u+1} (ZMod (p ^ n))
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : IsTopologicalAddGroup A := {
    continuous_add := continuous_of_discreteTopology
    continuous_neg := continuous_of_discreteTopology }
  let F : S.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget S ⋙ Over.forget S
  let E (U : S.ProEt) : C(U.left, A) ≃+ ULift.{u+1} (LocallyConstant U.left (ZMod (p ^ n))) :=
    { toFun := fun f => ⟨⟨fun x => (f x).down,
        ((IsLocallyConstant.iff_continuous (fun x => f x)).2 f.continuous).comp ULift.down⟩⟩
      invFun := fun r => ⟨fun x => ULift.up (r.down x),
        (r.down.isLocallyConstant.comp ULift.up).continuous⟩
      left_inv := by
        intro f
        apply ContinuousMap.ext
        intro x
        rfl
      right_inv := by
        intro r
        apply ULift.ext
        apply LocallyConstant.ext
        intro x
        rfl
      map_add' := by
        intro f g
        apply ULift.ext
        apply LocallyConstant.ext
        intro x
        rfl }
  have e : F.op ⋙ continuousMapPresheafAb A ≅ (liftedFiniteResidueProEtTower S p).obj (op n) :=
    NatIso.ofComponents (fun U => (E U.unop).toAddCommGrpIso) (by
      intro _ _ _
      apply AddCommGrpCat.hom_ext
      apply DFunLike.ext
      intro r
      rfl)
  have hbig : Presheaf.IsSheaf Scheme.proetaleTopology (continuousMapPresheafAb A) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb A)
  have hsmall : Presheaf.IsSheaf (Scheme.ProEt.topology S) (F.op ⋙ continuousMapPresheafAb A) :=
    F.op_comp_isSheaf_of_isSheaf (Scheme.ProEt.topology S) Scheme.proetaleTopology _ hbig
  exact (Presheaf.isSheaf_of_iso_iff e).1 hsmall

end RC53.EllAdic
