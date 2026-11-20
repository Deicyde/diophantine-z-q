module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Homeomorph.Lemmas

public section

/-! Universal subspaces have the ambient dimension, by the actual Mathlib
homeomorphism. No scheme presentation or extra geometric hypothesis is involved. -/

namespace CloudB3W16Dimension

/-- Dimension transport from the universal subspace to its ambient space. -/
theorem topologicalKrullDim_univ (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
  IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

end CloudB3W16Dimension
