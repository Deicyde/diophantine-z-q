import ZInQKernel.Contrib.HeightBC.H5GlueOpen

/-! # The original determinant lattice and its marked section under an open subgroup

This is the integral comparison needed to use the Néron identity-component model
in Gaudron–Rémond, Comment. Math. Helv. 89 (2014), §2.3, Definition 2.1. The open
inclusion and its generic isomorphism are the actual morphisms; the section is
transported by their cotangent pullback, not replaced by another generator.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Obj

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The actual Hodge pullback carries the actual integral lattice onto the lattice on the
open subgroup. The equality is of additive subgroups in its generic Hodge space. -/
theorem detLattice_map_openIso (G N : GroupModel A L) (j : G.G ⟶ N.G)
    [IsMonHom j] [IsOpenImmersion j.left] [IsIso ((Over.pullback (jL L)).map j)] (g : ℕ) :
    (N.detLattice g).toAddSubgroup.map (hodgeMap G N j g).toAddMonoidHom =
      (G.detLattice g).toAddSubgroup := by
  ext z
  change (∃ v ∈ N.detLattice g, hodgeMap G N j g v = z) ↔ z ∈ G.detLattice g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hodgeMap_detLattice G N j g v hv
  · exact detLattice_le_hodgeMap G N j g z

/-- The exact section at the target of cotangent pullback has the same index, with no
choice of a generator or positivity assumption about the index. -/
theorem secIndex_hodgeMap_openIso (G N : GroupModel A L) (j : G.G ⟶ N.G)
    [IsMonHom j] [IsOpenImmersion j.left] [IsIso ((Over.pullback (jL L)).map j)] (g : ℕ)
    (eta : N.hodgeSpace g) :
    secIndex (N.detLattice g) eta = secIndex (G.detLattice g) (hodgeMap G N j g eta) := by
  let E := hodgeMap G N j g
  have hi : IsIso ((Over.pullback (jL L)).map j) := inferInstance
  have hinj : Function.Injective E.toAddMonoidHom := (hodgeMapBijective K A L G N j hi g).1
  have h := (AddSubgroup.relIndex_map_map_of_injective
    (Submodule.span (𝓞 L) {eta}).toAddSubgroup (N.detLattice g).toAddSubgroup hinj).symm
  rw [map_span_singleton_toAddSubgroup E eta, detLattice_map_openIso G N j g] at h
  exact h

#print axioms detLattice_map_openIso
#print axioms secIndex_hodgeMap_openIso

end ZInQ.Contrib.IsogenyDegree
