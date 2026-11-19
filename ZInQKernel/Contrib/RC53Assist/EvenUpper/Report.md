# Conditional fixed-level even upper deductions

`SourceConsequenceInputs` is an explicitly conditional interface for numerical and cube consequences. It is not a certificate of actual-source provenance. The table `A` is unrestricted, and identifying it with the manuscript's normalized arithmetic coefficient symbol is an external obligation. The thirty original deductions are retained with consistent consequence-only names.

## Review corrections

### R1: provenance is external

The earlier name `FaithfulInputs` overstated what its type certifies. It is now `SourceConsequenceInputs`. Its fields still record the fixed level, central normalization, an exact relation between `W.Partitionable` and the formal table predicate, the guarded scalar comparison, a numerical unit bound, and a cube consequence. They do not assert coefficient rules, off-filter vanishing, a modular form, or equality with an actual coefficient source.

`SourceUnit W T A d` means only that the arbitrary table reads one on the prime configuration of a parameter in the negative squarefree support filter. `SourcePartitionable` similarly means a formal contraction certificate for that table. Neither name supplies arithmetic provenance.

`SuppliedMinimum` and `SquareReading` are numerical premises over arbitrary `aNZ`, `va`, and `κ`. They may hold for a singleton predicate at `W.kfin`. The unit-membership implication into `UnitMin` remains a separate premise. Their helper theorems are conditional arithmetic, not actual coefficient or minimum producers.

The literal minimum index remains `W.kfin`; no new minimizer is chosen or identified with it. Combining finitely many constants likewise chooses no minimum.

### R2: source and verification files are distinct

`Faithful.lean` is retained as the historical module filename. Its current declaration is `SourceConsequenceInputs`. The final source contains definitions and proofs only: no executable statement-printing or axiom-printing commands remain in it.

`statements-and-axioms.txt` is the preserved historical receipt, not a newly renamed receipt. It remains byte-for-byte unchanged:

```text
31590 bytes
SHA-256 d42108789cd72017f25acc7fd58aa7b4ca64a2018941b30c6384bc38482cb16d
```

The independent reviewer reproduced it from the earlier shipped body, which had 27424 bytes and SHA-256 `130677c6b2906fb3de556cd333afd137bd2c6b0ee76f9b68ccf670c5e5d1302b`. That body contained no executable checking commands. The receipt's old declaration names and the earlier instrumented-body hash are not claimed to describe the renamed source.

The earlier claim that a manifest was shipped has been removed. This report does not rely on that local historical manifest.

Current checking uses a **separate scratch file**, `.verification/SourceConsequenceAudit.lean`, consisting of an exact copy of the current final body followed by definition, statement, and axiom commands. Its output is `.verification/SourceConsequenceAudit.stdout`. The scratch file is verification evidence, not a final source module. Its 39207-byte prefix was compared byte-for-byte with the final source.

The final body and the instrumented scratch both compiled with exit code zero, without errors or warnings. The 30 retained deductions and six new genuine-source adapter theorems have 36 matching axiom reports. Every report contains exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Current verification identities:

```text
Faithful.lean: 39207 bytes
c9a2418347aa87eb37816047d2ccdf7f82bf40c973515ebcb7d5d9898c3568f2

.verification/SourceConsequenceAudit.lean: 42563 bytes
ad8fac21c3c0a921fc873c39f06c4878b9640dce72d5711ea3361c5726209bc9

.verification/SourceConsequenceAudit.stdout: 38804 bytes
01271e5b866e07f6953350dbca1213fba23ee9d867717cc6dc6890a0fbf7d0b8
```

[Current exact statements and axiom output](.verification/SourceConsequenceAudit.stdout) covers all 36 theorem declarations one-to-one. The historical receipt above is not renamed or overwritten.

Compilation uses the supplied individual-file command with six threads, the specified affinity, and no project build or dependency update. The exact command shape is:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 taskset -c 0-15 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/EvenUpper/Faithful.lean
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 taskset -c 0-15 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/EvenUpper/.verification/SourceConsequenceAudit.lean
```

## Conditional mathematical content

The fixed level is `N₀ ℓ = CST.newformLevel (Ecurve ℓ)`, not a free existential family level. `CurveLevel` separately requires a genuine functional-equation witness there. Positivity of the least cusp-form level follows from BCDT; the witness itself is not produced by that positivity argument.

`Scalar32` chooses one clearing exponent and one bounded error before the binary family. It requires a scalar for every `BinaryFamily (N₀ ℓ)`, integrality on all group-basis coefficients after clearing, both central-zero directions at corank-zero constituents, and the valuation comparison only when the central value is nonzero. The formula is

```text
v₂ u_h(0) = v₂ L_*(h) − 2ω(h) − s(h) + bounded error.
```

The numerical unit premise and the existing single-precision Boolean comparison give

```text
L_*(d) ≠ 0,
v₂ L_*(d) − 2ω(d) − s(d) ≤ C₀ + 2 C_loc.
```

The converse to corank zero uses the separate `Forward W` premise. It is not attributed to an equivalence printed in (3.3b). The singleton-family deduction also retains the conditional lower bound with constant `C_ev + C_loc`.

The fixed-source provenance requirement remains different from a sound conditional formula. Source construction is not discharged just because these conditional theorems have only standard axioms.

## Renamed consumer statements

The core namespace remains `ZInQ.Manuscript.RC.EvenUpperText`. With the usual implicit type-data parameters:

```lean
rc11Inputs_of_sourceConsequences :
  SourceConsequenceInputs W T A → EvenUpperRC11Inputs W

upper33b_of_sourceConsequences :
  Forward W → SourceConsequenceInputs W T A → ∃ C₁ : ℤ, Upper33b W C₁

currentUpper_of_sourceConsequences :
  Forward W → SourceConsequenceInputs W T A → ∃ C₁ : ℤ, EvenUpper33b W C₁
```

The full source-domain type is:

```lean
theorem sourceConsequence_upper_equivalence {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (hf : Forward W)
    (h : SourceConsequenceInputs W T A) :
    ∃ C₁ : ℤ, ∀ d : ℤ, SourcePartitionable W T A d →
      (Z2Corank (selmerTwoPower (Etw ℓ d)) 0 ↔
        W.Lstar d ≠ 0 ∧
          padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₁)
```

The current scratch output records every exact theorem type, including implicit binders and the renamed reading constructors, and every individual axiom report. The existing numerical consumer is reached by feeding `rc11Inputs_of_sourceConsequences h` to `evenUpper33b_of_RC11Inputs`, with its existing normalization and analytic premises. No consumer declaration is changed.

## Genuine-source adapter boundary

The separate genuine-source binding is `PreparedGenuineEvenSource` in `ZInQ.Contrib.RC53Assist.AuxFactor`. It ties the central normalization to `W.Lstar`, uses actual sign-minus-one `EvenPhaseData`, the original `S0Filter W.S D₀`, the already supplied phase-removed coefficient function and depth from `minimum_sieved`, and the equality of each prepared table with its actual dictionary symbol.

That producer is consumed only by import; it was not edited or reproduced. The new adapters derive the unit bound from its actual coefficients and existing depth, rather than assuming a numerical unit bound or using arbitrary `SuppliedMinimum` and `SquareReading` data:

- `unit_reading_of_genuine_source` derives the original `S0Filter`, nonzero canonical coefficient, and exact canonical depth from a value-one observation of the actual dictionary symbol.
- `unit_value_of_genuine_source` uses the supplied same-source coefficient-square identity to obtain the exact value
  `v₂ L_*(d) = 2ω(d) + 2δ_P + v₂ C.Lstar(-D₀)`, where `δ_P` is the already supplied `genuineEvenNormalization` depth.
- `units33a_of_preparedGenuineSources` combines the constants of the finitely many genuine prepared sources into one bound for all observed units.
- `sourceConsequenceInputs_of_preparedGenuineSources` derives the numerical unit-bound field and original normalization from that binding, retaining the remaining construction premises explicitly.
- `rc11Inputs_of_preparedGenuineSources` then supplies exactly the existing `EvenUpperRC11Inputs W` consumer.

No attained minimum index is selected by these adapters or identified with `W.kfin`; only the existing depth and coefficient functions are read. The old generic `SuppliedMinimum` helpers remain conditional numerical lemmas, and this genuine-source route does not use them.

The binding is only at `PreparedType`. For the global adapter the extra coverage premise is precisely:

```lean
∀ d : ℤ, SourceUnit W T A d →
  PreparedType W T (Symbols.primeConfig d.natAbs.primeFactors T.typ).total
```

This is not silently inferred from the consequence interface or from the prepared-source binding alone. `sourceUnit_type_prepared_of_zero_unprepared` proves it from the separate zero-extension specification:

```lean
∀ τ : L, ¬ PreparedType W T τ → ∀ Γ, A τ Γ = 0
```

The actual-source adapters also take the type-conductor support condition, the fixed-level scalar, the exact interface partitionability relation, and the stationary parameter-cube consequence. They do not construct those remaining inputs. Thus the result remains a conditional adapter, not a claim that the entire original `even_upper` leaf or all arithmetic source-construction obligations are discharged.

The supplied genuine-source module was read and imported without modification. Its source identity remained 13243 bytes, SHA-256 `c76a17245d63ba6776cae25aeae7e6eefda6c873d1c158f6b61a1585d917cd45`, before and after the adapter checks.

## Remaining obligations

For the authentic arithmetic application, provide:

1. The fixed-level functional-equation anchor, original central normalization, and the independent analytic forward theorem where used.
2. The original fixed-form scalar bundle at this exact level. `AppEOutputs` supplies it through the existing `scalar32_of_appE` deduction; no unspecified existential level is substituted.
3. Actual-source provenance and dictionary identities. Numerical `SuppliedMinimum` and `SquareReading` premises alone do not provide them.
4. The exact interface-to-formal partitionability relation and a genuine stationary parameter-cube construction. The scalar and unit bounds do not construct those cubes.
5. For a prepared-source adapter covering all formal units, membership of their total types in `PreparedType`.

The imported BCDT and Kolyvagin leaves are the only analytic leaves needed by the forward-rank compatibility route. `forward_of_weil_leaves` keeps the weak-Weil parametrization passage and its stated analytic-to-algebraic translation gap separate. No new printed theorem, phase transport, old-to-new unit source, ratio assembly, or field assembly is supplied here.

The independent review is the basis for narrowing the provenance claims. The earlier proof receipt and published evidence are preserved rather than rewritten as evidence for the new names.
