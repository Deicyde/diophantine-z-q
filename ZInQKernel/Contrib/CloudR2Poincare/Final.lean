import ZInQKernel.Contrib.CloudR2Poincare.Reduction
import ZInQKernel.Contrib.CloudR2Poincare.L2.B4Assembly
import ZInQKernel.Contrib.CloudR2Poincare.ProjectiveEmbedding
import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientDescentCompatibility
import ZInQKernel.Contrib.CloudR2Poincare.L2.NormalGraphProjection
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedGlobalSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Surjectivity
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientExists

/-!
# H-72: `PoincareComplement` from named inputs, the round-2 end state (CONDITIONAL)

Round 2, 2026-11-14.

`poincareComplement_of_inputs` derives the fixed target `ZInQ.Contrib.AVB1.PoincareComplement` from seven named
`Prop`s. It is **not** a proof of the target, and none of the inputs is assumed anywhere as a fact. Each input is a
true, standard statement.

| input | statement | classical source |
|---|---|---|
| `L2.ReducedGlobalNormalizedSeesaw` | seesaw on a reduced locally noetherian base | Mumford §5 Cor. 6 |
| `L2.PicZeroPointSurjectivityFromSquare` | square ⇒ every translation-invariant class is `t_b^*M ⊗ M⁻¹` | Mumford §8 Thm 1 |
| `L4.FiniteStabilizerQuotientExists` | quotient of an abelian variety by a finite stabilizer subgroup scheme | Mumford §12 Thm 1; Stacks 07S6 |
| `L2.NativeTheoremOfTheSquare` | theorem of the square in families (over `T` with `Pic T = 0`) | Mumford §6 Cor. 4 |
| `L2.NativeQuotientDescentCompatibility` | the Mumford family is constant along the stabilizer action | **proved from the seesaw** (`L2.nativeQuotientDescentCompatibility_of_seesaw`) |
| `L2.NativeProjectiveEmbeddingExists` | abelian varieties are projective | **proved** (`nativeProjectiveEmbeddingExists_proof`, H70 C4) |
| `L2.NativeNormalGraphProjectionCriterion` | proper, reduced, bijective on geometric points onto smooth `J`, char 0 ⇒ iso | **proved** (`L2.nativeNormalGraphProjectionCriterion_proof`) |

Proved in this campaign, with no remaining inputs:
* `L3.KernelComplement_proof`;
* `L4.ComplementIsogeny_proof`;
* `L3.NativeLerayDegeneration_proof`;
* `L4.stabilizerAbVarQuotientExists_of_quotient`, which supplies all of the quotient's abelian-variety geometry;
* the graph construction and its point bijection (`L2.GraphMorphism`, `L2.QuotientPoint…`);
* Ω-coverage of the original stabilizer;
* `L2.finite_translationStabilizer_of_globalSeesaw`.
-/

namespace ZInQ.Contrib.CloudR2Poincare

/-- **H-72 from seven named inputs (conditional).** -/
theorem poincareComplement_of_inputs
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    (hB2 : L2.PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : L2.NativeTheoremOfTheSquare.{0})
    (hCompatibility : L2.NativeQuotientDescentCompatibility)
    (hEmbedding : L2.NativeProjectiveEmbeddingExists)
    (hGeometry : L2.NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_polarizationRetract
    (L2.polarizationRetract_of_inputs hA hB2 hQuotient hSquare hCompatibility hEmbedding hGeometry)

/-- **H-72 from six named inputs (conditional).** The projective embedding is discharged by H70 C4
(`nativeProjectiveEmbeddingExists_proof`). -/
theorem poincareComplement_of_six_inputs
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    (hB2 : L2.PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : L2.NativeTheoremOfTheSquare.{0})
    (hCompatibility : L2.NativeQuotientDescentCompatibility)
    (hGeometry : L2.NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_inputs hA hB2 hQuotient hSquare hCompatibility
    nativeProjectiveEmbeddingExists_proof hGeometry

/-- **H-72 from five named inputs (conditional).** The projective embedding is discharged by H70 C4; the
quotient-descent compatibility is derived from the seesaw (`L2.nativeQuotientDescentCompatibility_of_seesaw`). -/
theorem poincareComplement_of_five_inputs
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    (hB2 : L2.PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : L2.NativeTheoremOfTheSquare.{0})
    (hGeometry : L2.NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_polarizationRetract
    (L2.polarizationRetract_of_inputs' hA hB2 hQuotient hSquare
      nativeProjectiveEmbeddingExists_proof hGeometry)

/-- **H-72 from four named inputs (conditional).** Projective embedding (H70 C4), quotient-descent
compatibility (from the seesaw) and the normal-graph criterion (`L2.nativeNormalGraphProjectionCriterion_proof`)
are discharged. Remaining: seesaw, B2 from the square, quotient existence, theorem of the square. -/
theorem poincareComplement_of_four_inputs
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    (hB2 : L2.PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : L2.NativeTheoremOfTheSquare.{0}) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_five_inputs hA hB2 hQuotient hSquare
    L2.nativeNormalGraphProjectionCriterion_proof

/-- **H-72 from three named inputs (conditional).** Discharged since the four-input form: the seesaw
(`L1.ReducedGlobalNormalizedSeesaw_proof`) and B2 (`L3.picZeroPointSurjectivity_of`, from the seesaw, the square and
the vanishing B1). Remaining: the Pic⁰-vanishing B1, quotient existence, theorem of the square. -/
theorem poincareComplement_of_three_inputs
    (hB1 : L3.NativePicZeroVanishing.{0})
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : L2.NativeTheoremOfTheSquare.{0}) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_four_inputs L1.ReducedGlobalNormalizedSeesaw_proof
    (fun hSq => L3.picZeroPointSurjectivity_of L1.ReducedGlobalNormalizedSeesaw_proof hB1 hSq)
    hQuotient hSquare

/-- **H-72 from two named inputs (conditional).** The finite-stabilizer quotient is discharged by
`L4.FiniteStabilizerQuotientExists_proof`, which uses the borrowed H5 FLT provider
`ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`.
Remaining: the Pic⁰ cohomology vanishing B1 and the theorem of the square. -/
theorem poincareComplement_of_two_inputs
    (hB1 : L3.NativePicZeroVanishing.{0})
    (hSquare : L2.NativeTheoremOfTheSquare.{0}) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_three_inputs hB1 L4.FiniteStabilizerQuotientExists_proof hSquare

end ZInQ.Contrib.CloudR2Poincare
