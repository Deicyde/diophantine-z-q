import ZInQKernel.OneProof.H.TailP
import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Dimension

/-!
# H-100: finite type group schemes are equidimensional

The target is the unchanged `AVGlue.GroupSchemeEquidim` from `TailP`.
The dimension comparison is Stacks Tag 045X, supplied by the immutable
AxiomMath/Stacks snapshot recorded in the supporting source manifest.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every irreducible component of a finite type group object over a field has
its ambient topological Krull dimension. -/
theorem groupSchemeEquidim_proof : AVGlue.GroupSchemeEquidim := by
  intro k _ G _ hft hqc Z hZ
  letI : LocallyOfFiniteType G.hom := hft
  letI : QuasiCompact G.hom := hqc
  letI : G.left.Over (Spec (CommRingCat.of k)) := ⟨G.hom⟩
  letI : GrpObj (G.left.asOver (Spec (CommRingCat.of k))) := by
    change GrpObj G
    infer_instance
  letI : LocallyOfFiniteType (G.left ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType G.hom
    exact hft
  have he := equidimensional_of_groupScheme k G.left
  obtain ⟨W, hW, -, hd⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      k G.left G.hom hZ.1.nonempty.some
  exact (he Z hZ W hW).trans
    (hd.trans (topologicalKrullDim_eq_topologicalKrullDimAt_of_groupScheme
      k G.left hZ.1.nonempty.some).symm)
