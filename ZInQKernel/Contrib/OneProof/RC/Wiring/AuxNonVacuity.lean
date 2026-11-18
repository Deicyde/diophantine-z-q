import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3
import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.RedeiFilter

/-!
# Theorem 5.3, Lane RC0: the corrected auxiliary-factor and even-upper shapes are consistent

A concrete instance of the corrected data specifications, on batch 3's interface data `W₂ ℓ`
(support `{2}`, prepared filter `{1}`, `Partitionable` the Rédei partitionability on the corrected
filter of negative squarefree odd parameters; `EvenUpper.W₂`), PROVED:

* `preparedSpec_W₂'`: the corrected `PreparedSpec` (positive, squarefree, `≡ 1 (mod 8)`, prime to the
  support);
* `auxFactorInputs_W₂`: all five corrected clauses of `AuxFactorInputs` (batch 3's
  `auxClauses_W₂`, whose prepared types are this file's `PreparedType`);
* `auxFactor_W₂`: the auxiliary factor itself, by the dictionary argument at the prepared types;
* `consistency_W₂`: these together with a nonempty `Partitionable` (`−7`, batch 3's
  `partitionable_W₂_neg7`) and the single-precision even input at the same data (batch 3's
  `evenUpperInputsAt_W₂`).

Not covered here: the genuine arithmetic clauses ((3.2) for the genuine normalization of `L_*`,
the realized cubes at every partitionable parameter), which need genuine data.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- The corrected `PreparedSpec` for batch 3's data `W₂` (PROVED: batch 3's `preparedSpec_W₂`). -/
theorem preparedSpec_W₂' (ℓ : ℕ) : PreparedSpec (EvenUpper.W₂ ℓ) :=
  EvenUpper.preparedSpec_W₂ ℓ

/-- **All five corrected clauses of `AuxFactorInputs` hold for `W₂`** (PROVED: batch 3's
`auxClauses_W₂` over the sign type data and the filtered Rédei symbols). -/
theorem auxFactorInputs_W₂ (ℓ : ℕ) : AuxFactorInputs (EvenUpper.W₂ ℓ) :=
  ⟨ZMod 2, inferInstance, inferInstance, AddMonoidHom.id (ZMod 2), signTypeData, EvenUpper.Afam,
    EvenUpper.auxClauses_W₂ ℓ⟩

/-- **The auxiliary factor for `W₂`** (PROVED: `auxFactor_of_prepared`, the support `{2}`). -/
theorem auxFactor_W₂ (ℓ : ℕ) : ∃ A₀ : ℕ, AuxFactor (EvenUpper.W₂ ℓ) A₀ := by
  obtain ⟨L, iL, fL, ε, T, A, hmS, hA, hoff, hseed, hspec⟩ := auxFactorInputs_W₂ ℓ
  refine @auxFactor_of_prepared ℓ (EvenUpper.W₂ ℓ) (fun p hp => ?_) (Finset.mem_singleton_self 2)
    L iL fL ε T hmS A hA hoff hseed hspec
  rw [show (EvenUpper.W₂ ℓ).S = {2} from rfl, Finset.mem_singleton] at hp
  rw [hp]
  exact Nat.prime_two

/-- **Consistency of the corrected shapes** (PROVED): at batch 3's data `W₂`, the corrected
prepared filter, all five aux clauses, a nonempty `Partitionable` and the single-precision even
input hold together. -/
theorem consistency_W₂ (ℓ : ℕ) :
    PreparedSpec (EvenUpper.W₂ ℓ) ∧ AuxFactorInputs (EvenUpper.W₂ ℓ) ∧
      (EvenUpper.W₂ ℓ).Partitionable (-7) ∧ EvenUpper.EvenUpperInputsAt (EvenUpper.W₂ ℓ) :=
  ⟨preparedSpec_W₂' ℓ, auxFactorInputs_W₂ ℓ, EvenUpper.partitionable_W₂_neg7 ℓ,
    EvenUpper.evenUpperInputsAt_W₂ ℓ⟩

end ZInQ.Manuscript.RC.Wiring
