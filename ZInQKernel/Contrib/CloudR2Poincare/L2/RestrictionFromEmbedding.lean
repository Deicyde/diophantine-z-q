import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmple

/-!
# Consumption of C4's exact projective-embedding conclusion

H70 C4 exclusively owns and proves the general projective embedding theorem.
This internal L2 interface consumes its literal conclusion as an explicit input;
it constructs no embedding, imports no other worktree, and assumes no global
existence Fact. Once C4 is integrated, its theorem is exactly the argument for
`hProjectiveEmbedding` below.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- C4's exact output supplies `O(1)` on the actual `J` and its very ample
restriction to the actual closed abelian subvariety `B`. This is conditional
only on the explicit, separately owned projective-embedding conclusion. -/
theorem exists_veryAmple_closedRestriction_of_projectiveEmbedding
    {k : Type u} [Field k] (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J)
    (hi : IsClosedImmersion i.hom.left)
    (hProjectiveEmbedding :
      ∃ (coordinates : Type u) (_ : Finite coordinates)
        (embedding : J.X.left ⟶ ℙ(coordinates; Spec (.of k))),
        IsClosedImmersion embedding ∧
          embedding ≫ ℙ(coordinates; Spec (.of k)) ↘ Spec (.of k) = J.X.hom) :
    ∃ L : J.X.left.Modules,
      L.IsInvertible ∧ VeryAmple J.X.hom L ∧
      ((Scheme.Modules.pullback i.hom.left).obj L).IsInvertible ∧
      VeryAmple B.X.hom ((Scheme.Modules.pullback i.hom.left).obj L) := by
  obtain ⟨coordinates, hfinite, embedding, hembedding, hπ⟩ := hProjectiveEmbedding
  let L := ProjectiveSpace.twistRestrict embedding 1
  have hvery : VeryAmple J.X.hom L :=
    ⟨coordinates, hfinite, embedding, hembedding, hπ, ⟨Iso.refl _⟩⟩
  have : L.IsInvertible := hvery.isInvertible
  letI : IsClosedImmersion i.hom.left := hi
  refine ⟨L, inferInstance, hvery, inferInstance, ?_⟩
  simpa only [i.hom.w] using hvery.closedRestriction i.hom.left

end ZInQ.Contrib.CloudR2Poincare.L2
