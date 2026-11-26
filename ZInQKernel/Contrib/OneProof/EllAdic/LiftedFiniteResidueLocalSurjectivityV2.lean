import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueDiagonalV1
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace RC53.EllAdic

universe u

/-- The actual constant diagonal is locally surjective: a locally constant
section restricts to its value on the corresponding open fibre. The covers
are open subschemes of the same small pro-étale object. -/
theorem liftedResidueConstantDiagonal_locallySurjective (S : Scheme.{u}) (p n : ℕ) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology S)
      (liftedResidueConstantDiagonal S p n) where
  imageSieve_mem {U} r := by
    change ULift.{u+1} (LocallyConstant U.left (ZMod (p ^ n))) at r
    let fibre (a : ZMod (p ^ n)) : U.left.Opens :=
      ⟨{x | r.down x = a}, r.down.isLocallyConstant.isOpen_fiber a⟩
    have hfibre : IsOpenCover fibre := by
      change (⨆ a, fibre a) = ⊤
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact (Opens.mem_iSup (x := x) (s := fibre)).2 ⟨r.down x, rfl⟩
    let cov := U.left.openCoverOfIsOpenCover fibre hfibre
    let V (a : ZMod (p ^ n)) : S.ProEt :=
      Scheme.ProEt.mk ((fibre a).ι ≫ U.hom)
    let j (a : ZMod (p ^ n)) : V a ⟶ U :=
      MorphismProperty.Over.homMk (fibre a).ι rfl
    let R : Presieve U := Presieve.ofArrows V j
    have hcover : R ∈ Scheme.ProEt.precoverage S U := by
      change R ∈ (Scheme.proetalePrecoverage.comap (Scheme.ProEt.forget S ⋙ Over.forget S)) U
      rw [Precoverage.mem_comap_iff]
      change (Presieve.ofArrows V j).map (Scheme.ProEt.forget S ⋙ Over.forget S) ∈
        Scheme.proetalePrecoverage U.left
      rw [Presieve.map_ofArrows]
      change cov.presieve₀ ∈ (Scheme.qcPrecoverage ⊓
        Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u})) U.left
      refine ⟨Scheme.zariskiPrecoverage_le_qcPrecoverage _ cov.mem₀, ?_⟩
      refine (Scheme.presieve₀_mem_precoverage_iff cov.toPreZeroHypercover).2 ⟨?_, ?_⟩
      · intro x
        exact ⟨cov.idx x, cov.covers x⟩
      · intro i
        change WeaklyEtale (fibre i).ι
        infer_instance
    apply (Scheme.ProEt.topology S).superset_covering
      ((Sieve.generate_le_iff R _).2 ?_) (Precoverage.generate_mem_toGrothendieck hcover)
    intro W f hf
    change Presieve.ofArrows V j f at hf
    cases hf with
    | mk a =>
      change ∃ t : ULift.{u+1} (ZMod (p ^ n)),
        (liftedResidueConstantDiagonal S p n).app (op (V a)) t =
          ((liftedFiniteResidueProEtTower S p).obj (op n)).map (j a).op r
      refine ⟨ULift.up a, ?_⟩
      apply ULift.ext
      apply LocallyConstant.ext
      intro x
      change a = r.down ((fibre a).ι x)
      exact x.property.symm

end RC53.EllAdic
