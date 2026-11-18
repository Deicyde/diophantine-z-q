# Fixed-field arithmetic budget: corrected primary export

## Correction edition (2026-11-18)

The primary export is now `ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_from_selmer_minimal`, found in an independent review. It derives the rank bound from the residual exact sequence of (5.7c), (5.7a), and positive central Smith valuations, following manuscript lines 5355–5359. It does not consume `SmallGradedModel`.

The previous claim that `SmallGradedModel` derived the rank bound was incorrect. Its arbitrary injections and prescribed basis sizes assume degreewise rank inequalities. The old exports remain available, with that assumption stated explicitly. No embedding of this kind is attributed to the manuscript.

The corrected `ArithmeticBudget.lean` is 85,259 bytes, SHA-256 `487675f4bcba8d28cb5178f63f25bdfdfd0f7476dc8506117b1a5909c179212b`. Its shipped source contains no statement-inspection or axiom-inspection commands. `Audit.md` and `Verification.log` preserve the earlier instrumented edition's evidence; they are historical records, not verification of this corrected edition. Their theorem bodies remain unchanged, but the earlier interpretation of the nonminimal rank route is superseded here. The stale instrumented-edition checksum file is not part of this edition.

Base source revision: `a6c70bd54e403ce3ead8ff2b8e40f80445fe58cc`. The correction was made against the reviewed contribution edition. No version-control operation was performed.

## Target and every field in plain mathematics

The unchanged target is `ZInQ.Contrib.CloudB3RC53.ClearingComplex.BudgetInputsAt`, defined in `ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel`, lines 266–279. Write `D_c` for the central Smith complex, `C_K` for the ordinary compact Kummer Selmer complex, and `J_r = H²(Q_r)`. Lengths are over the 2-adic integers; the target's free-generator function is `(0,1,1,0)`.

1. **Total chain rank:** the sum of ranks in degrees zero through three is at most `2 d_K + 12`. Manuscript lines 5279–5283, 5355–5359, 5385–5386.
2. **Four cohomology modules:** the existential modules represent `H¹(C_K)`, `H²(C_K)`, `J_r`, and `H³(C_K)`, with their additive and scalar structures. Lines 5251–5259, 5350–5351, 5362–5364.
3. **Degree-one comparison:** `H¹(D_c) ≅ H¹(C_K)`. Line 5362.
4. **Exact sequence:** `0 → H²(C_K) → H²(D_c) → J_r → H³(C_K) → H³(D_c) → 0`, including left injectivity and right surjectivity. Lines 5363–5364.
5. **Degree-one torsion:** `length H¹(C_K)_tors = t_K`, with arithmetic `t_K = length E(K)[2^∞]`. Lines 5257–5259 and 5285–5295.
6. **Degree-three length:** `length H³(C_K) = t_K`, from integral Kummer self-duality and universal coefficients. Lines 5296–5302, equation (5.7b).
7. **Degree-two torsion:** `length H²(C_K)_tors = h_K`; this is the definition of `h_K`, not an independent estimate. Lines 5257–5263.
8. **Singular length:** `length J_r ≤ 2 c_E`, from the two rank-two singular determinant caps and their retained limit. Lines 5320–5334 and 5336–5351.
9. **First free rank:** `rank H¹(C_K) = 1`. Lines 5264–5267 and 5304–5312.
10. **Second free rank:** `rank H²(C_K) = 1`. Lines 5304–5312.

The disk count is not a separate target field. The Smith identities `rank_total = 2 + 2m` and `hSmith = total torsion length` yield `m ≤ d_K + 5` and `hSmith ≤ h_K + 2c_E + 2t_K` once the target fields hold. Lines 5366–5386.

## Exact primary statement

All names below are in `ZInQ.Contrib.RC53Assist.Budget`, with the imported `BudgetInputsAt`, `fr₀`, `SmithBlocks`, `OO`, and `dualCx`.

```lean
theorem budgetInputsAt_from_selmer_minimal {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (P : IntegralFirstSmithModel A)
    (dK hK cE tK : ℕ) (R : RetainedSingularStage A cE)
    (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (hdual : IntegralModelDuality P.C) (hpar : ParameterAgreement A dK hK tK) :
    BudgetInputsAt B fr₀ dK hK cE tK
```

Its proof composes `budgetInputsAt_of_integralModel`, `residuallyMinimal_of_positive`, `residualKummerProfile_of_selfDuality`, `R.bounds`, and the parameter-renaming theorem. This route uses the residual comparison fields that were unused by the former primary export. It does not assume the total or degreewise rank budget through an arbitrary injection. It does impose positive central valuations: it is the manuscript's minimal-model route, not a theorem allowing arbitrary unit disks with no size control.

## Derived facts and their inputs

- **Residual profile (5.7a):** `dualHomologyEquiv` computes cohomology of a field-valued dual with no finite-dimensionality assumption on cochain terms. `residualKummerProfile_of_selfDuality` derives the upper dimensions and their finiteness from `γ`, rank-two degree-zero invariants and degree-one finiteness. `genuine_residual_profile` supplies this through the existing manuscript-cited `NekovarProp543` and genuine truncated pairing/isotropy and orthogonality data. It does not demand full-target isotropy.
- **Rank bound:** `residuallyMinimal_of_positive B hpos` identifies chain rank with residual cohomology rank. `ArithmeticComparison.rank_budget` then uses the residual cochain exact sequence, source and singular quasi-isomorphisms, and the central residual comparison. The source contributes `2 d_K + 4`, and two rank-two disks contribute at most eight. This is the primary rank derivation at lines 5355–5359.
- **(5.7d):** `ArithmeticComparison.h1Equiv` and `exact_sequence` derive the degree-one isomorphism and the full degree-two/three sequence from cochain exactness and singular cohomology vanishing. `GenuineComparison.toArithmetic` proves the cochain exactness with `galoisChangeCondSES_shortExact`. Cohomology exactness is not assumed.
- **Singular length:** principal-ideal-domain Smith normal form gives cokernel length equal to determinant valuation. `R.bounds` and `ArithmeticComparison.singular_length` derive `length J_r ≤ 2 cE`. The input is a determinant cap; `RetainedSingularStage` alone does not bind its witnesses to actual moving-prime stage matrices.
- **Torsion parameters:** `length_parameters` derives finiteness and the natural values of ordinary degree-one and degree-two torsion lengths from the Smith comparisons. `h_K` is cohomologically definitional, not a bound on the whole Tate–Shafarevich group.
- **(5.7b):** `IntegralFirstSmithModel.dual_h3_length` computes degree-three cohomology of the finite free model's dual from its first Smith differential. `length_comparison` derives the length equality from the separate `IntegralModelDuality` input. No length equality is a premise of the primary export; no termwise duality of infinite integral cochains or self-injectivity of the 2-adic integers is asserted.
- **Free ranks:** `free_ranks` derives both from `fr₀`, the integral comparison and the finite singular quotient. This is redundancy removal at the fixed pattern, not an independent proof of the analytic full-corank-one theorem.
- **Disk and valuation consequences:** the existing `ArithmeticComparison.smith_budget` is valid with residual minimality, the derived profile and singular bounds, and `P.length_comparison`. On the primary route it uses `residuallyMinimal_of_positive`, not `SmallGradedModel`. The degree-range condition is automatic for `BlockComplex.toSmithBlocks`, whose `n` is three.

## Consumed interfaces and honest boundaries

1. **`ArithmeticComparison B`:** integral and residual cochain short exact sequences for (5.7c); central integral cohomology comparisons in degrees one through three; central residual comparisons in degrees zero through three; an ordinary residual source comparison; singular quasi-isomorphisms for two integral matrices and their reductions. These are canonical-comparison inputs, not numerical budget inputs. The primary route uses all these comparison fields.
2. **`IntegralFirstSmithModel A`:** a finite free ordinary source model, a quasi-isomorphism to the integral first term, and just its first differential split into the same first Smith coordinates. The remaining differentials are constrained only by the complex equations.
3. **`hpos`:** all central Smith valuations are positive. It corresponds to the unit cancellation choice in lines 5357–5359. An actual old model containing central unit disks needs either cancellation and compatible comparisons or an explicitly assumed size bound.
4. **`IntegralModelDuality`:** a separate `def … : Prop` for self-duality of the ordinary finite free model. It is the model-level consequence of the cited integral/adic Selmer duality theorem, not a proof of its arithmetic instantiation.
5. **`RetainedSingularStage`:** coefficient-precision witnesses with determinant nonvanishing and valuation caps. Without actual-stage bindings, nonemptiness is equivalent to the same cap on the limit matrices; choose the witnesses equal to the limits for one direction. The singular length remains a derived consequence of that cap.
6. **`ParameterAgreement`:** only a rename of `A.dK`, `A.hK`, `A.tK`. It holds by reflexivity at computed values. It proves no identification with `Sel₂(E/K)` or `E(K)[2^∞]`. The scalar `cE` is not included in this rename and is **not tied to the manuscript's constant**.
7. **Genuine constructor:** `GenuineComparison.toArithmetic` consumes `galoisSelData` and `GaloisCondInclusion` for integral and residual coefficients and ordinary/full conditions. It does not require degreewise isomorphisms of full continuous local cochains with a finite tame model.

### Legacy nonminimal route

`SmallGradedModel` is an **assumed degreewise rank-bound input**, not a consequence of (5.7c). Its basis size and arbitrary injection encode

```text
rank D_cⁿ ≤ dim Hⁿ(ordinaryRed) + rank Q_rⁿ.
```

No compatibility is imposed on those injections. Its `phi` and `qis` fields are unused by the rank proof and by the former primary export. The seven residual-comparison fields of `ArithmeticComparison` are also unused by that old export. Accordingly `budgetInputsAt_from_selmer_models`, `budgetInputsAt_of_smallGradedModel`, and `smith_budget_of_smallGradedModel` are retained only as compatibility results; their rank and disk-count conclusions inherit an assumed rank bound. Their theorem statements and proof bodies have not been changed.

## Precisely what remains

This correction is a conditional reduction, not an unconditional canonical discharge of target (7).

- Instantiate the actual Tate representation, residual `E[2]`, and derived ordinary Kummer conditions including degree-zero torsion; supply the invariant comparison, Selmer-two identification and degree-one finiteness.
- Construct the retained integral and residual scalar comparisons and central coefficient-change identifications for the actual final-field limiting diagram, including the singular quasi-isomorphisms. A fixed-prime finite-stage condition change is not silently identified with the retained limit.
- Supply the actual unit-cancelled old Smith model with `hpos`, preserving the required central integral/residual comparisons. If central unit disks must remain, the nonminimal route still needs an explicitly stated rank-bound input; this correction does not prove that input.
- Supply the ordinary finite free first-Smith model and instantiate `IntegralModelDuality` from integral/adic Selmer duality with the genuine Weil pairing and derived Kummer orthogonal diagrams. Finite-ring `NekovarFiniteSetting` is not applied to the 2-adic integers.
- Bind the determinant-cap witnesses and `cE` to actual moving Frobenius/point-count data and the manuscript's fixed constant. The present natural-number cap has no such binding.
- Identify the computed cohomological parameters with the manuscript's arithmetic parameters. `dK_of_selmer_identification` and `tK_of_coefficient_exact` provide algebraic conversion routes; `ParameterAgreement` is just the final rename.

## Manuscript-cited source

The integral model-duality input cites Jan Nekovář, *Selmer complexes*, Astérisque 310 (2006), theorem 6.3.4, printed p. 143, with hypotheses 6.2.5–6.2.8 on pp. 139–140. The printed theorem has a derived-category error term and gives an isomorphism for orthogonal complements. Transport to the actual finite free ordinary model remains explicit.

The edition and passages were read in the Numdam scan: https://www.numdam.org/item/AST_2006__310__R1_0.pdf . The residual genuine producer reuses the existing proposition 5.4.3 interface and truncated Selmer-duality proof. No new axiom is declared.

## Verification of the corrected edition

Both the final uninstrumented source and a separate scratch copy compiled successfully with the prescribed affinity, priority and thread limit. The scratch copy checked the exact conclusion of the new primary theorem and audited **all 57 theorems and 20 proof-producing definitions**. Every axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`; the new primary uses exactly those three. Each run had zero errors and eight unchanged style/unused-tactic warnings.

`ReviewCompile.log` records the shipped-source compile. `ReviewVerification.log` records the scratch statement and axiom output. `ReviewAudit.md` reproduces every checked statement and its actual axiom output. The scratch source was removed after verification so inspection commands are not delivered in Lean files. The source hash above identifies the exact file compiled.

## Delivery boundary

Only the owned budget contribution was changed: the new primary theorem and corrected documentation. Existing proof bodies, target definitions, other contributions, identification reconstruction and dependency pins remain unchanged. No version-control operation, project build, dependency update, external message or integration operation was performed. The stale checksum file is removed; earlier published proof and audit history is preserved.
