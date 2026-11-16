import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Zero-dimensional abelian varieties: singleton schemes and rational points

A locally Noetherian irreducible scheme of dimension at most zero is a singleton:
Mathlib's Artinian criterion gives the discrete topology, and irreducibility then
forces a single point. Over an algebraically closed field, the bijection between
rational points and closed points makes the rational-point group a singleton.

These are prerequisites for the zero-dimensional cases of analytic uniformization
and GAGA. They do not prove either universally quantified OneProof field.

Reuse: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
`AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero` (Brian Nugent),
`Topology.IsDiscrete.subsingleton_of_isPreirreducible`, and
`AlgebraicGeometry.ext_of_apply_closedPoint_eq` (Andrew Yang).
The project `PkgI3.AbVar`, its dimension, and its points are used unchanged.
-/

open CategoryTheory AlgebraicGeometry Set

noncomputable section

namespace CloudB3W17.ZeroDim

/-- A locally Noetherian irreducible scheme of dimension at most zero is a singleton. -/
theorem subsingleton_scheme_of_dim_le_zero (X : Scheme) [IsLocallyNoetherian X]
    [IrreducibleSpace X] (hX : topologicalKrullDim X ≤ 0) : Subsingleton X := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hX
  have : DiscreteTopology X := inferInstance
  refine ⟨fun x y => ?_⟩
  exact DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible
    (PreirreducibleSpace.isPreirreducible_univ : IsPreirreducible (univ : Set X))
    (mem_univ x) (mem_univ y)

/-- A zero-dimensional abelian variety over an algebraically closed field has one rational point. -/
theorem subsingleton_pts_of_dim_le_zero {k : Type} [Field k] [IsAlgClosed k]
    (A : PkgI3.AbVar k) (hA : A.dim ≤ 0) : Subsingleton (A.Pt k) := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : Subsingleton A.X.left := subsingleton_scheme_of_dim_le_zero A.X.left hA
  refine ⟨fun p q => ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq A.X.hom
  · simpa [PkgI3.AbVar.ptObj] using Over.w p
  · simpa [PkgI3.AbVar.ptObj] using Over.w q
  · exact Subsingleton.elim _ _

end CloudB3W17.ZeroDim
