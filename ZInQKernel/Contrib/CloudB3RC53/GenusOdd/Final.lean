import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Node34
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.TwistDescentProof

/-!
# GenusOdd: (3.4) with the reduced GLUE

`TwistDescent` is PROVED (`twistDescent_proof`), so the GLUE of (3.4) reduces to four inputs:
`ArtinFactorization`, `NeronTateTwist` (Néron–Tate functoriality), `GenusTheory`,
`SplittingCriterion`. (Since then `NeronTateTwist` (`HeightDischarge.lean`) and
`SplittingCriterion` (`Splitting/Criterion.lean`) are PROVED and the current route is
`Artin34.lean` / `LocalFinal.lean`.)
-/

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- The remaining GLUE of (3.4) (each one a `Prop` of `Glue.lean`, flagged GLUE). -/
structure GlueReduced : Prop where
  artin : ArtinFactorization
  height : NeronTateTwist
  genus : GenusTheory
  split : SplittingCriterion

theorem glue34_of_reduced (G : GlueReduced) : Glue34 :=
  ⟨G.artin, G.height, twistDescent_proof, G.genus, G.split⟩

/-- **(3.4)** (Proposition `ex:sec7-genus-lower`, tex L2418–2439) from the printed leaves and the
reduced GLUE. -/
theorem genusLower34_of_reduced (P : Prints) (G : GlueReduced) : GenusLower34 :=
  genusLower34_proof P (glue34_of_reduced G)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
