import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.HDecomp.Faltings.HodgeLattice

/-!
# The local facts of hodge-lattice at the origin of an abelian variety, and `HodgeLatticeTheorem`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task infra-smooth-dim, `scratch/infra-smooth-dim/HodgeLatticeClosed.lean` §6).

The kernel module `ZInQKernel.HDecomp.Faltings.HodgeLattice` proves
`hodgeLatticeTheorem_of_abVarFacts : RegularAtOrigin → DimAtOrigin → DimBaseChange →
HodgeLatticeTheorem`. This file proves the kernel's own statements (not copies):

* `regularAtOrigin : RegularAtOrigin` and `dimAtOrigin : DimAtOrigin`, from
  `topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth` (an abelian variety is smooth and
  irreducible, and its origin is a closed point);
* `dimBaseChange : DimBaseChange`, which is g9-abvarbc's `PkgI3.AbVar.dim_baseChange`
  (`ZInQKernel/Contrib/AbVarBC/Dim.lean`);
* `tangentDimAtOrigin : TangentDimAtOrigin`;
* **`hodgeLatticeTheorem : ZInQ.DefFaltings.HodgeLatticeTheorem`**, with no hypotheses.
-/

namespace ZInQ.Contrib.Dim

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj IsLocalRing
open ZInQ.DefFaltings.HodgeLattice

/-- The origin of an abelian variety is a closed point. -/
theorem isClosed_originPt {L : Type} [Field L] (B : PkgI3.AbVar L) :
    IsClosed ({originPt B} : Set B.X.left) := by
  have := isClosedImmersion_of_comp_eq_id (Y := Spec (CommRingCat.of L)) B.X.hom
    (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left (by simp)
  have hr : Set.range (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left.base =
      {originPt B} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : Subsingleton (PrimeSpectrum L) := inferInstance
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum L) a ⟨⊥, Ideal.isPrime_bot⟩)
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr]
  exact (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left.isClosedEmbedding.isClosed_range

/-- At the origin of an abelian variety `B`, the local ring has Krull dimension `dim B`, and its
maximal ideal needs exactly that many generators. -/
theorem originPt_dims {L : Type} [Field L] (B : PkgI3.AbVar L) :
    B.dim = ringKrullDim (B.X.left.presheaf.stalk (originPt B)) ∧
      ((maximalIdeal (B.X.left.presheaf.stalk (originPt B))).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (B.X.left.presheaf.stalk (originPt B)) := by
  have : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := B.X.hom)
  exact topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth B.X.hom (originPt B)
    (isClosed_originPt B)

/-- **hodge-lattice's `RegularAtOrigin`, proved** (kernel statement): the local ring of an abelian
variety at its origin is regular. -/
theorem regularAtOrigin : RegularAtOrigin := by
  intro L _ B
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  exact (isRegularLocalRing_iff _).mpr (originPt_dims B).2

/-- **hodge-lattice's `DimAtOrigin`, proved** (kernel statement): the local ring of an abelian
variety of dimension `g` at its origin has Krull dimension `g`. -/
theorem dimAtOrigin : DimAtOrigin := by
  intro L _ B g hg
  rw [← (originPt_dims B).1, hg]

/-- **hodge-lattice's `DimBaseChange`, proved** (kernel statement; g9-abvarbc's proof). -/
theorem dimBaseChange : DimBaseChange := by
  intro K _ A L _ _
  exact PkgI3.AbVar.dim_baseChange A L

/-- **hodge-lattice's `TangentDimAtOrigin`, proved** (kernel statement): the cotangent space of an
abelian variety of dimension `g` at its origin has dimension `g`. -/
theorem tangentDimAtOrigin : TangentDimAtOrigin :=
  tangentDimAtOrigin_of regularAtOrigin dimAtOrigin

/-- **`HodgeLatticeTheorem`, proved with no hypotheses** (kernel statement,
`ZInQKernel/HDecomp/Faltings/Models.lean`). -/
theorem hodgeLatticeTheorem : ZInQ.DefFaltings.HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_abVarFacts regularAtOrigin dimAtOrigin dimBaseChange

end ZInQ.Contrib.Dim
