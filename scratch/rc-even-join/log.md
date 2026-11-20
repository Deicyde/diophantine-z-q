# Sizing and results

- VERIFIED: merged the unary head `03f1ba32a0cf267ff4b7814770812eb08027a235` into the moving base.
- VERIFIED: `EvenExpansion.evenExpansion` (Assembly.lean) has the following type, with `hS : SupportSpec W`, `X : EvenBudget.Model P hS B`, `[CharZero X.K]`, `A : O12.FourierData X` and `C : EvenBudget.SourceAtPlace P X.O X.K` fixed:
  ```lean
  (i : Fin 2) (U : Finset ℕ)
  (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
  (f : WeightTwo (movingLevel P U))
  (hf : ∀ n, (qExpansion 1 f).coeff n =
    timesTheta (halfDivided (evenTypes W.S hS.1).Good
      (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n)
  (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
  (hcoord : ∀ n, n ≠ 0 → κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
    (qExpansion 1 f).coeff n) :
  ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n
  ```
  The exact coordinate input is `hcoord` under the same `κ` and `hκ`. The budget quantifies `∀ U, (∀ p ∈ U, Good p) → U.card + 1 ≤ B → ...` inside the choice of place, model and Fourier data; it does not quantify over subsets of a finite pool.
- VERIFIED: `EvenMoving.evenMovingSieve` and `EvenUnary.evenUnaryStageLaw` supply the two premises of `EvenExpansion.evenWeightTwo`. Each shell index is positive by `ThetaCoeff.mem_subscripts`. The assembled form need not have one character.
- VERIFIED: `EvenBudget.commonCoeff_complex` and `commonCoeff_place` identify the two images of the formal series; the depth shift cancels here. `EvenExpansion.evenVector_eval` evaluates the formal combination once the moving and each unary block are given coordinates.
- VERIFIED: `BlocksPerU.HasWeightTwoExpansion` refers to genuine Gamma1 weight-two forms and records the pulled-back character and positive expansion. `spansAt_of_complex` descends characterwise complex spanning for a fixed `Inventory` whose columns already lie in the field. `coordinates_of_span` picks coordinates supported only on columns of the correct character and level. `ThetaCoeff.Blocks.coeff_F` computes the coefficient of `Blocks.F` because the latter is constructed from the chosen coordinates. This odd construction covers subsets of a given finite pool.
- VERIFIED: `GaloisConstituentModel` takes `coefK`, `expand`, and `F` as data. `expand_spec` and `FourierData.expand_coeff` allow evaluating model coordinates but do not identify the model's seeds with a particular modular form. The manuscript fixes a stage and U before choosing a finite complete field (tex 9649–9654) and requires retention of the individual level and character sectors (9754–9764). The budget-level compatibility of those choices, realization of the inventory, and construction of the model seeds from those coordinates are not supplied by this passage or by the two transformation laws.

- VERIFIED: serial `lake build` completed for `EvenUnary.Complete`, `EvenMoving.Assembly` and `BlocksPerU.Descent`, with `LEAN_NUM_THREADS=4`. Missing artifacts were restored from source-identical parent caches before the successful builds; the first cold dependency run was stopped before restoring the cache.
- VERIFIED: `Joined.lean` passed direct `lake env lean -j1` and its module build. `joinedForm` is chosen from the closed moving and unary assembly; `joinedForm_coeff` proves its exact all-index expansion. `evenExpansion_joined` has the exact transfer type above with `f := joinedForm hS i U hU hodd` and the supplied proof `hf` removed. `budgetRealization_of_joined` supplies the even row with the same `κ` for every tested set.
- VERIFIED: `Coordinates.lean` passed direct `lake env lean -j1` and its module build. The moving and unary block coefficient series and characters descend under one `κ`; the existing complex-span and coordinate theorems then retain each block's intrinsic level and character. Their linear combination gives `evenSeed` with the expansion of `joinedForm`.
- VERIFIED: `coordinate_match_of_seed` requires comparison of the field Fourier maps on the embedded inventory and the seed identity in the model. The exact comparison then follows from the model's two existing coefficient identities. For `B ≥ 2`, `no_common_level` excludes a single positive level for the whole budget, even using just singleton tests.
- VERIFIED: `lake env lean -j1 scratch/rc-even-join/Audit.lean` passed. All 21 printed axiom sets (19 theorems and 2 definitions, including private helpers) are contained in `{propext, Classical.choice, Quot.sound}`.
- OPEN: instantiate the characteristic-zero inventories and the simultaneous place/model/seed comparison at tex 9649–9654 and 9754–9764. No coefficient equality for an arbitrary preselected model is implied by its structure fields.
