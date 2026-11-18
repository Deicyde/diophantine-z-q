import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Inputs
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic

/-!
# Theorem 5.3, Lane RC0 round 3: the even upper bound (3.3b) from RC11's inputs

The leaf `PreLeaves.even_upper` asked for `EvenUpperInputs W`: (3.3a) at the units, (3.2), and the
missing address on the cubes at every precision. Batch 3's EvenUpper replaces it by the
single-precision form `EvenUpperInputsAt` (the one precision `C₀ + C_loc + c_E + 1` its consumer
uses; tex 2322–2341, 10114–10125) and builds that from lane RC11's normalization and (3.2)
(`EvenScalar32`), the realized cubes of units, and (3.3a) at the units, with the Boolean comparison
on the cubes (the missing address, clause (iii)) PROVED from lane RC1 (`evenUpperInputsAt_of`).
`evenUpper33b_of_RC11Inputs` (PROVED) gives `∃ C₁, EvenUpper33b W C₁` from `EvenUpperRC11Inputs W`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-- **The remaining inputs of (3.3b)** (Proposition `ex:sec7-even-upper`, tex 2273–2341; App G
(F.1)–(F.2), 10079–10129):
* `unitSym`, `C₀`, (3.3a): the units of the normalized even symbol have `L_*(p) ≠ 0` and
  `v₂L_*(p) ≤ 2ω(p) + C₀` (ELLIOT; tex 2302–2310, App E `ex:app-even-phase`; owner RC11; batch 3's
  `h33a_of_F1` derives it from (E.11) and (E.9));
* (3.2): lane RC11's `EvenScalar32` for its normalization of `L_*` (ELLIOT; tex 1966–1968, App E
  (E.8); owner RC11);
* the realized cubes: for every partitionable `d` with Selmer corank zero and every dimension, a
  binary family of parameters based at `d` whose nonzero addresses are units of the symbol (ELLIOT;
  tex 2311–2322, App G 10100–10129; owner batch 3 EvenUpper / RC2). -/
def EvenUpperRC11Inputs {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (unitSym : ℤ → Prop) (C₀ : ℤ) (N₀ : ℕ),
    (∀ p, unitSym p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀) ∧
    (∀ L : Even.CentralNormalization (Ecurve ℓ), L.Lstar = W.Lstar →
      Even.EvenScalar32 (Ecurve ℓ) N₀ L) ∧
    (∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧ Function.Injective fam.h ∧
        ∀ x, x ≠ 0 → unitSym (fam.h x))

/-- **(3.3b) from RC11's inputs** (PROVED: batch 3's `evenUpperInputsAt_of` and
`evenUpper33b_of_inputsAt`, with the Kummer sequence in rank zero proved). -/
theorem evenUpper33b_of_RC11Inputs {ℓ : ℕ} (W : WData ℓ) (P : Prints) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (hN : LstarNormalized W.toRCData)
    (h : EvenUpperRC11Inputs W) : ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨unitSym, C₀, N₀, h33a, h32, hcubes⟩ := h
  obtain ⟨L, hLW⟩ := hN
  exact EvenUpper.evenUpper33b_of_inputsAt W P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hℓ hL
    (EvenUpper.evenUpperInputsAt_of W unitSym C₀ h33a L hLW (h32 L hLW) hcubes)

end ZInQ.Manuscript.RC.Wiring
