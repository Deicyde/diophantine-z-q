# Fixed-field arithmetic budget: interface analysis


## Shipped edition (2026-11-18)

The shipped `ArithmeticBudget.lean` (82648 bytes, SHA-256 `5802de543046b226e9bda6eb69435d65e5ff2b27b281a8b4e1ddbea9cdf15752`) is the checked source with its `#check` and `#print axioms` lines removed; `Audit.md` and `Verification.log` record the output of the instrumented edition. The checksum file of the instrumented edition is not shipped.

Base source revision: `a6c70bd54e403ce3ead8ff2b8e40f80445fe58cc`.

The consumed target is `ZInQ.Contrib.CloudB3RC53.ClearingComplex.BudgetInputsAt`, defined in `ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel`, lines 266–279. No identification structure or cancellation construction is changed.

## Mathematical meaning of every target field

Write `D_c` for the central Smith complex, `C_K` for the ordinary compact Kummer Selmer complex, and `J_r = H²(Q_r)`. All lengths below are over the 2-adic integers. The free-generator function used by the clearing model is `(0,1,1,0)`.

1. **Total chain rank:** the sum of the ranks of `D_c^0, D_c^1, D_c^2, D_c^3` is at most `2 d_K + 12`. Manuscript lines 5279–5283, 5355–5359, 5385–5386.
2. **Cohomology modules and scalar structures:** the four existential modules represent `H¹(C_K)`, `H²(C_K)`, `J_r`, and `H³(C_K)`. Manuscript lines 5251–5259, 5350–5351, 5362–5364.
3. **Degree-one comparison:** `H¹(D_c)` is linearly isomorphic to `H¹(C_K)`. Manuscript line 5362.
4. **Degree-two/three comparison:** there are linear maps making the sequence `0 → H²(C_K) → H²(D_c) → J_r → H³(C_K) → H³(D_c) → 0` exact, including injectivity at the left and surjectivity at the right. Manuscript lines 5363–5364. This must come from the cohomology sequence of the actual comparison in (5.7c), not an assumed arithmetic sequence.
5. **Degree-one torsion:** `length H¹(C_K)_tors = t_K`, where `t_K = length E(K)[2^∞]`. Manuscript lines 5257–5259 and 5285–5295.
6. **Degree-three length:** `length H³(C_K) = t_K`, from integral Kummer self-duality and universal coefficients. Manuscript lines 5296–5302, equation (5.7b).
7. **Degree-two torsion:** `length H²(C_K)_tors = h_K`. This is the definition of `h_K`, not an independent arithmetic estimate. Manuscript lines 5257–5263.
8. **Singular length:** `length J_r ≤ 2 c_E`. Each of the two rank-two singular differentials has nonzero determinant of valuation at most `c_E`; these facts survive the retained limit at precision `c_E + 1`. Manuscript lines 5320–5334 and 5336–5351.
9. **First free rank:** `rank H¹(C_K) = 1`. Manuscript lines 5264–5267 and 5304–5312.
10. **Second free rank:** `rank H²(C_K) = 1`. Manuscript lines 5304–5312. A finite singular cokernel cannot change this free rank.

## Consequences requested by (5.7)

The disk count is not a separate field of `BudgetInputsAt`. For Smith disks in source degrees zero, one and two, the proved identity is `rank_total D_c = 2 + 2 m`, including unit disks. It yields `m ≤ d_K + 5` (lines 5375–5386). The sum of the valuations of all nonzero Smith entries equals the total torsion length (lines 5382–5383); the exact sequence gives the bound `h_K + 2 c_E + 2 t_K` (lines 5366–5373).

## Existing proved interfaces available for reuse

- `RankCounts.finrank_centralH`, `sum_finrank_centralCx`, `sum_length_torsion_centralH_amp`, and `budget_rank`: exact Smith-chain, cohomology, disk, and valuation counts.
- `RankCounts.sum_finrank_centralRed`: residual dimension of a minimal central Smith model.
- `RankCounts.singularDiskLimit_proof`: bounded determinant valuation is stable under entrywise congruence at the retained precision.
- `Determinant.singular_complex_cohomology` and `singular_complexes_total_length_le`: injectivity and singular cokernel lengths.
- `SelmerComplex.galoisChangeCondSES_shortExact`: the actual condition-change short exact sequence for genuine continuous Galois cochains.
- `GenuineInst.finrank_homology_dualCx`: complementary cohomology dimensions under field-valued self-duality, with no finite-dimensionality assumption on the cochain terms.

The distinction between chain rank and cohomology rank is essential. Quasi-isomorphy alone does not bound the size of a nonminimal model: arbitrary unit disks can be added without changing its cohomology. A rank derivation must therefore consume minimality or an explicit retained bound on such disks.

## Verified result

`ArithmeticBudget.lean` supplies a conditional arithmetic/model reduction to the unchanged target. It is not an unconditional instantiation for the final family and does not claim to complete the restricted converse.

The primary export is `ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_from_selmer_models`. Its exact statement is:

```lean
theorem budgetInputsAt_from_selmer_models {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A)
    (dK hK cE tK : ℕ) (R : RetainedSingularStage A cE)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (hdual : IntegralModelDuality P.C) (hpar : ParameterAgreement A dK hK tK) :
    BudgetInputsAt B fr₀ dK hK cE tK
```

The source contains statement checks and axiom checks for every theorem, including private algebraic helpers, and for the proof-producing definitions. The successful single-file verification audited **56 theorems and 20 proof-producing definitions**. The union of their axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`. There were no errors and eight style/unused-tactic warnings. `Audit.md` contains every checked statement and its actual axiom output, verbatim.

### Fields now derived, and how

- **Residual profile (5.7a):** `dualHomologyEquiv` proves the cohomology-of-dual calculation over a field without assuming finite-dimensional cochain terms. `residualKummerProfile_of_selfDuality` derives both upper dimensions and their finiteness from self-duality, degree-zero rank-two invariants, and degree-one finiteness. `genuine_residual_profile` obtains that self-duality from the existing manuscript-cited `NekovarProp543`, genuine truncated pairing/isotropy data, and Kummer orthogonality. It does not impose the stronger full-target isotropy condition.
- **Total chain rank:** `SmallGradedModel.rank_budget` derives `2 d_K + 12` from an ordinary minimal source model and embeddings of the old graded modules into that model plus the two singular disks. `singular_chain_total_rank` computes the added chain rank as eight. This version allows surviving unit disks. The alternative `ArithmeticComparison.rank_budget` uses residual minimality of the old model; `residuallyMinimal_of_positive` proves that property from positive central valuations.
- **Degree-one comparison and the entire (5.7d) sequence:** `ArithmeticComparison.h1Equiv` and `exact_sequence` derive them from a short exact sequence of cochain complexes and vanishing of singular cohomology in degrees zero, one and three. The genuine constructor proves both cochain short exact sequences using `galoisChangeCondSES_shortExact`. No cohomology exactness field is an input.
- **Singular bound:** the local cokernel length is proved from principal-ideal-domain Smith normal form and equals the determinant valuation. `singularBounds_of_retained` derives nonzero limiting determinants and their bounds from congruence at precision `c_E + 1`, using `RankCounts.singularDiskLimit_proof`. Consequently `ArithmeticComparison.singular_length` derives `length J_r ≤ 2 c_E`; it is not assumed.
- **Finite natural torsion parameters:** `length_parameters` derives finiteness of the degree-one and degree-two torsion lengths. The first is the first Smith cokernel length, and the second embeds into the finite second Smith torsion module. The computed parameters are the natural values of those ordinary source lengths; `h_K` is a definition, not a separate estimate.
- **Degree-three length (5.7b):** `IntegralFirstSmithModel.dual_h3_length` computes degree-three cohomology of the termwise dual of a finite free ordinary model from only its first Smith differential. `length_comparison` then derives `length H³(C_K) = length H¹(C_K)_tors` from the separately stated `IntegralModelDuality` input. The stronger producers do not assume a length equality. No termwise duality is asserted for infinite continuous cochains over the 2-adic integers, and the integers are not asserted to be self-injective.
- **Both free ranks:** `free_ranks` derives them from the fixed generator pattern, the source comparison, and the finite singular quotient. `budgetInputsAt_of_rankless` formally drops the two free-rank hypotheses from the other original fields with no replacement hypothesis. This is a redundancy removal at `fr₀`, not a new proof of the analytic full-corank-one theorem.
- **Disk and valuation budgets:** `smith_budget_of_smallGradedModel` gives exactly `B.mTot ≤ A.dK + 5` and `B.hSmith ≤ A.hK + 2 c_E + 2 A.tK`, using the proved `RankCounts.budget_rank`. All Smith disks, including units, are counted. The degree-range input is automatic for `BlockComplex.toSmithBlocks`, whose `n` is three.
- **Fixed-field invariance and arithmetic names:** `parameters_eq` proves that the three parameters depend only on ordinary source cohomology. `dK_of_selmer_identification` and `tK_of_coefficient_exact` provide explicit arithmetic binding routes. The latter proves that an exact Kummer coefficient sequence against torsion-free rational cohomology identifies the rational point torsion group with integral cohomology torsion; no torsion-length premise is used.

## Exact consumed interfaces

1. **Target:** `ClearingComplex.BudgetInputsAt B fr₀ dK hK cE tK`, at `fr₀ = (0,1,1,0)`. No identification structure is consumed or changed.
2. **Scalar comparison:** `ArithmeticComparison B` contains an integral cochain short exact sequence for (5.7c), its residual counterpart, cohomological comparisons with `centralH` in degrees one through three and `centralRed` in degrees zero through three, and quasi-isomorphisms from the two-disk singular models. Its ordinary residual source maps quasi-isomorphically to the residual sequence's first term. The residual singular matrices are the reductions of the same integral matrices.
3. **Genuine constructor:** `GenuineComparison.toArithmetic` uses `galoisSelData` and `GaloisCondInclusion` for fixed `K`, support, integral coefficients, residual coefficients, and ordinary/full local conditions. It proves cochain exactness rather than taking that exactness as data. Full continuous local complexes are never required to be degreewise isomorphic to two-term or three-term tame complexes.
4. **Small retained graded model:** `SmallGradedModel` gives a quasi-isomorphic ordinary finite free source model, bases of its residual minimal sizes, and injective embeddings of old graded modules into the source plus the singular terms. This is the model-size/coefficient-change interface for the rank estimate, not the estimate itself. The old model may be nonminimal.
5. **Integral model:** `IntegralFirstSmithModel` gives a finite free ordinary model mapping quasi-isomorphically to the integral sequence's first term, a split first Smith differential in the same first Smith coordinates, and no assumptions on its other matrices beyond the complex equations.
6. **Source duality input:** `IntegralModelDuality` is a separate `def … : Prop` expressing self-duality on that finite free ordinary model. The finite-coefficient genuine duality path instead uses the existing separately stated `NekovarProp543` and `OrthogonalComplementsT` interfaces.
7. **Retained arithmetic precision:** `RetainedSingularStage` gives one stage matrix at each place, congruence at the sufficient precision, and the stage determinant nonvanishing and valuation cap. Limiting determinant and cokernel facts are conclusions.
8. **Parameter binding:** `ParameterAgreement` records equality with the manuscript's parameter names. These are definition/identification links; they contain no rank, disk or torsion-budget estimate.

## Precisely what remains open

The numerical implications and cohomology-sequence implications are verified. The following canonical instantiations are not supplied here:

- Identify the chosen integral representation with `T₂E`, the residual representation with `E[2]`, and the ordinary local conditions with the genuine derived Kummer conditions, including degree-zero torsion. Supply the actual degree-zero invariant comparison, degree-one finiteness and identification with the arithmetic Selmer-two group.
- Construct the retained integral and residual comparisons for the actual final-field limiting diagram, including both singular quasi-isomorphisms and the central Smith cohomology comparisons. This still includes coefficient change from the old family/augmentation model to the 2-adic central model. The finite-stage genuine condition-change constructor is proved, but taking and identifying the retained limit is not silently assumed to be the same as choosing one fixed prime.
- Supply the ordinary minimal model, its coefficient-change bases and the old graded embeddings used by `SmallGradedModel` (or residual minimality for the alternative producer).
- Supply the finite free ordinary model and first Smith comparison of `IntegralFirstSmithModel`, and instantiate `IntegralModelDuality` from the integral/adic Selmer duality theorem with the actual Weil pairing and derived Kummer orthogonal diagrams. The existing finite-ring `NekovarFiniteSetting` is not applied to the 2-adic integers. The weaker compatibility producer still accepts `IntegralKummerLengthComparison`; the primary model producer derives that comparison instead.
- Bind the retained stage determinant cap to the actual moving Frobenius/point-count data, rather than merely to abstract matrices and a natural `c_E`.
- For the original arithmetic parameter names, supply `ParameterAgreement`. In particular the actual rational two-primary point group and its coefficient-sequence maps must instantiate `tK_of_coefficient_exact`. No assertion about finiteness of the whole two-primary Tate–Shafarevich group is required.

Thus this is **not yet an unconditional canonical discharge of target (7)**. It replaces the former assumed numerical budget and cohomology exact sequence by explicit lower-level genuine/model interfaces and verified consequences. Nothing about graph cancellation, identification reconstruction, or coordinate clearing was edited.

## Manuscript-cited source check

The source for the new integral duality input is Jan Nekovář, *Selmer complexes*, Astérisque 310 (2006), theorem 6.3.4, printed p. 143, with hypotheses 6.2.5–6.2.8 on printed pp. 139–140. The printed theorem states a derived-category duality triangle with an error term and gives an isomorphism for orthogonal complements. Passing that conclusion to a finite free ordinary model is an explicit model-level input here; a source reading does not itself prove its canonical instantiation.

The relevant edition and passages were read in the Numdam scan: https://www.numdam.org/item/AST_2006__310__R1_0.pdf . The finite residual producer reuses the existing stated proposition 5.4.3 and the existing truncated Selmer-duality proof, rather than introducing a new printed axiom.

## Delivery boundary

Only new contribution files were written. Existing sources and dependency pins were left alone. No version-control operation, project build, dependency update, Lake executable-target run, external message, or integration operation was performed. Single-file typechecking used the prescribed affinity, priority and thread limit. Missing compiled helpers were not built: the required scalar dual-homology and determinant-length arguments were re-established locally from available Mathlib and contribution interfaces. The unavailable central-fibre helper was not imported.
