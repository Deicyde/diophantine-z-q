import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Cubes
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper3

/-!
# EvenUpper, part 7: the even upper inputs without distinct cube parameters

The corrected shape of RC0's `EvenUpperRC11Inputs` (`RC/Wiring/EvenUpper3.lean`): clause (iii)
asks for the realized cubes without `Function.Injective fam.h`. Batch 3's `evenUpperInputsAt_of'`
(`Cubes.lean`) does not need distinct parameters: the representative address of a parameter is
chosen after the Boolean comparison. All `PROVED`:

* `EvenUpperRC11InputsNI W`: RC0's inputs with the injectivity dropped;
* `evenUpperRC11InputsNI_of`: RC0's inputs give the corrected ones;
* `evenUpper33b_of_RC11InputsNI`: `∃ C₁, EvenUpper33b W C₁` from the corrected inputs, through
  `evenUpperInputsAt_of'` and the proved Kummer sequence in rank zero.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring

/-- **The remaining inputs of (3.3b), corrected** (RC0's `EvenUpperRC11Inputs` without the
injectivity of the cube parameters; tex 2273–2341). -/
def EvenUpperRC11InputsNI {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (unitSym : ℤ → Prop) (C₀ : ℤ) (N₀ : ℕ),
    (∀ p, unitSym p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀) ∧
    (∀ L : Even.CentralNormalization (Ecurve ℓ), L.Lstar = W.Lstar →
      Even.EvenScalar32 (Ecurve ℓ) N₀ L) ∧
    (∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧
        ∀ x, x ≠ 0 → unitSym (fam.h x))

/-- RC0's inputs are the corrected ones (`PROVED`: RC0's `EvenUpperRC11Inputs` no longer asks
the cube parameters to be distinct, so the two bodies are identical). -/
theorem evenUpperRC11InputsNI_of {ℓ : ℕ} (W : WData ℓ) (h : EvenUpperRC11Inputs W) :
    EvenUpperRC11InputsNI W := h

/-- **(3.3b) from the corrected inputs** (`PROVED`: `evenUpperInputsAt_of'` and
`evenUpper33b_of_inputsAt`, with the Kummer sequence in rank zero proved). -/
theorem evenUpper33b_of_RC11InputsNI {ℓ : ℕ} (W : WData ℓ) (P : Prints) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (hN : LstarNormalized W.toRCData)
    (h : EvenUpperRC11InputsNI W) : ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨unitSym, C₀, N₀, h33a, h32, hcubes⟩ := h
  obtain ⟨L, hLW⟩ := hN
  exact evenUpper33b_of_inputsAt W P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hℓ hL
    (evenUpperInputsAt_of' W unitSym C₀ h33a L hLW (h32 L hLW) hcubes)

end ZInQ.Contrib.CloudB3RC53.EvenUpper
