# Full-degree after-t rank counts at the active witness

## Result

`activeAfterTCounts_full` applies `residualRankCounts_afterT''` to `actSel`,
`afterP`, `afterP'`, and `afterL`. Every rank sum is over `Finset.Icc (0 : ℤ) 3`.
The reduction and generic base-change comparisons are the complex isomorphisms
`witness_ered` and `witness_ebc`; the global degree-three input is
`witness_eG3 h410`.

The condition sum remains exactly the Kummer-row sum. The shifted local sum
now includes local `H²` and equals the whole local dimension sum. The integral
smaller-support model has support `[0, 3]`; the supports and degreewise
finiteness of the generic models are supplied by `afterP'_ge`, `afterP'_le`,
`afterL_ge`, `afterL_le`, `afterP'_finite`, and `afterL_finite` from
`ZInQKernel/Contrib/RC53Assist/ResidualWitnessActive/Witness.lean`.

The final bound is `2 ≤ genericRank ≤ rankTot` and `genericRank ≤ 294`.
The total rank includes the cone's degree-three local term, not merely degrees
zero through two.

## Source and compilation

Source: `ZInQKernel/Contrib/RC53Assist/ResidualWitnessAfterT/Witness.lean`.

- Size: 9322 bytes.
- SHA256: `e38200730b93f15979327a9c6e620c91d1a33ab46eeccbf875c5997f75de6d50`.
- Single-file compilation: exit code 0, no diagnostics.
- Temporary diagnostic copy: exit code 0; all ten new declarations and five
  reused comparison or positivity declarations were audited.
- Compilation used six Lean threads, processor affinity 96–111, and niceness 10.
- The source declares a heartbeat limit of 600000.
- No pre-existing source or compiled file was modified by this contribution.

The single-file command within the repository was:

```text
lake env lean ZInQKernel/Contrib/RC53Assist/ResidualWitnessAfterT/Witness.lean
```

## Exact declaration statements

All the new declarations below are in
`ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT`. Their unqualified names refer to
that namespace. The statements use the same open namespaces as the source.

### Global comparison

```lean
def actEG_full (n : ℤ) (hn : n ∈ Finset.Icc (0 : ℤ) 2) :
    actSel.G.X n ≃ₗ[ZMod 2]
      genH SmallK (primesAboveSet SmallK (chargedPrimes 66 5 actD)) n.toNat
```

### Exact condition sum

```lean
theorem act_hUm_full_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p
```

### Private local calculation

```lean
private theorem place_L_full_dims (v : Places SmallK SmallS) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((locCC v.1).homology (n - 1)) =
      genLocDim SmallK SmallS v.1
```

### Exact local sum

```lean
theorem act_hLm_full_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) =
      ∑ p ∈ chargedPrimes 66 5 actD, genLocSum SmallK SmallS p
```

### Integral support

```lean
theorem afterP_supported (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterP.IsStrictlyGE 0 ∧ afterP.IsStrictlyLE 3
```

### Constructor application

```lean
def activeAfterTCounts_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts
```

### Whole generic rank

```lean
theorem activeAfterTCounts_full_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts_full h410 h51 h28 h23).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n)
```

### Whole integral rank

```lean
theorem activeAfterTCounts_full_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts_full h410 h51 h28 h23).rankTot =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((selCx actSel).X n)
```

### Final after-t count statement

```lean
theorem residualRankCounts_afterT_active_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (activeAfterTCounts_full h410 h51 h28 h23).genericRank ∧
      (activeAfterTCounts_full h410 h51 h28 h23).genericRank ≤
        (activeAfterTCounts_full h410 h51 h28 h23).rankTot ∧
      (activeAfterTCounts_full h410 h51 h28 h23).genericRank ≤ 294
```

### Direct rank-sum statement

```lean
theorem afterT_full_rank_estimate (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n) ∧
      (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n)) ≤
        (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((selCx actSel).X n)) ∧
      (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n)) ≤ 294
```

## Axiom audit from temporary diagnostics

The temporary diagnostic compilation reported the following dependencies.
Only the three standard axioms occur. The private helper is recorded under its
source-level name rather than the generated private name of the diagnostic copy.

```text
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.actEG_full
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.act_hUm_full_eq
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.place_L_full_dims
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.act_hLm_full_eq
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.afterP_supported
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.activeAfterTCounts_full
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.activeAfterTCounts_full_genericRank
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.activeAfterTCounts_full_rankTot
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.residualRankCounts_afterT_active_full
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT.afterT_full_rank_estimate
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.CloudB3RC53.GenuineInst.witness_ered
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.CloudB3RC53.GenuineInst.witness_ebc
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.CloudB3RC53.GenuineInst.witness_eG3
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessActive.afterE
  depends on axioms: [propext, Classical.choice, Quot.sound]
ZInQ.Contrib.RC53Assist.ResidualWitnessActive.two_le_afterL_zero
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What remains

There are no remaining inputs for this full-degree constructor application.
Its conclusions are conditional on the four explicit Milne hypotheses:
`MilneADT_I_4_10_totallyComplex`, `MilneADT_I_5_1_totallyComplex`,
`MilneADT_I_2_8`, and `MilneADT_I_2_3_trivial`.

The witness still uses a constant power-series extension of the residual cone
and a split original-support model. Constructing the global character with the
specified active Frobenius values, the corresponding arithmetic power-series
and Laurent-series cochains, and their limit and comparison maps remains
outside this contribution. This application alone is not the proof of
Theorem 5.3.
