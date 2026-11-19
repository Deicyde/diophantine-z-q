import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8
import ZInQKernel.Contrib.RC53Assist.FrobeniusTraceDictionary.Proved

/-!
# The trace of Frobenius on `T₂E` is a theorem

`FrobeniusTrace E` (at every good odd prime `r`, an arithmetic Frobenius at `r` acts on the
`2`-adic Tate module with trace `a_r`) follows, with no remaining input, from

* the trace dictionary `goodReductionFrobeniusTraceDictionaryQ_proved` (a contributor's
  `RC53Assist/FrobeniusTraceDictionary/Proved.lean`: the reduction comparison of Tate modules,
  `TateReduction.tateReductionComparison`, and the determinant formula
  `det(1 − nπ) = 1 − a n + p n²`, `DetDegree.frobeniusTateDetFormOne_proved`), and
* the local–global comparison `localGlobalFrobenius_proof` (`CommonCoordinate8.lean`: a global
  arithmetic Frobenius lifts to an arithmetic Frobenius of `Gal(ℚ̄_r/ℚ_r)`, and the global and local
  Tate modules are identified compatibly).

So the common-coordinate leaf needs no Frobenius input at all: `CommonCoordinateInputsNF` keeps only
the coefficient datum and the step triangles, and implies the round-two leaf
(`commonCoordinateInputsLF_of_NF`), hence (4.7) (`commonCoordinateTarget_of_NF`). Tex 4142–4328
(Lemma `ex:arith-common-coordinate`); Silverman AEC V.2.3.1, VII.3.1(b), VII.4.1.
-/

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

/-- **The trace of Frobenius on `T₂E`** (PROVED, no input): for an elliptic curve `E/ℚ`, at every
good odd prime the trace of an arithmetic Frobenius on `T₂E` is `a_r`. -/
theorem frobeniusTrace_proved (E : WeierstrassCurve ℚ) [E.IsElliptic] : FrobeniusTrace E :=
  frobeniusTrace_of_dictionary E
    ZInQ.Contrib.RC53Assist.FrobeniusTraceDictionary.goodReductionFrobeniusTraceDictionaryQ_proved
    (localGlobalFrobenius_proof E)

/-- **The common-coordinate inputs with no Frobenius input** (definition): `E_ℓ` elliptic, a
coefficient datum, and the step triangles at every address of a final family. -/
def CommonCoordinateInputsNF {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateTrianglesLF ℓ hE C D F x)

/-- **The round-two leaf from the triangles alone** (PROVED, through `frobeniusTrace_proved`). -/
theorem commonCoordinateInputsLF_of_NF {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsNF D) :
    CommonCoordinateInputsLF D := by
  obtain ⟨hE, C, hT⟩ := h
  exact ⟨hE, C, @frobeniusTrace_proved (Ecurve ℓ) hE, hT⟩

/-- **The round-two leaf is equivalent to the triangles alone** (PROVED). -/
theorem commonCoordinateInputsLF_iff_NF {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsLF D ↔ CommonCoordinateInputsNF D := by
  constructor
  · rintro ⟨hE, C, -, hT⟩
    exact ⟨hE, C, hT⟩
  · exact commonCoordinateInputsLF_of_NF

/-- **(4.7) from the triangles alone** (PROVED). -/
theorem commonCoordinateTarget_of_NF {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsNF D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_LF (commonCoordinateInputsLF_of_NF h)

end ZInQ.Manuscript.RC.Wiring
