import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusRootsProof
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LstarBridge
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# GenusOdd: (3.4) from the printed leaves and two GLUE statements

With `GenusRoots` (`genusRoots_proof`) and the splitting criterion
(`Splitting.splittingCriterion_proof`, the Splitting area) proved, the GLUE of (3.4) is
`ArtinFactorization` (the `L`-factorization of the ring-class `L`-function) and `RingClassGalois`
(`H_c/ℚ` Galois). This file packages the endpoints at that GLUE. (`RingClassGalois` is no longer
needed on the route of `Artin34.lean`, and `ArtinFactorization` is reduced in `LocalFinal.lean`.)
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- The remaining GLUE of (3.4). -/
structure GlueTwo : Prop where
  artin : ArtinFactorization
  galois : RingClassGalois

theorem glueAfterRC19_of_two (G : GlueTwo) : GlueAfterRC19 :=
  glueAfterRC19_of_final ⟨G.artin, G.galois, genusRoots_proof,
    ZInQ.Contrib.CloudB3RC53.Splitting.splittingCriterion_proof⟩

/-- **(3.4)** from the printed leaves and `GlueTwo`. -/
theorem genusLower34_of_two (P : Prints) (G : GlueTwo) : GenusLower34 :=
  genusLower34_of_RC19 P (glueAfterRC19_of_two G)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
