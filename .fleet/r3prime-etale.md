# r3prime-etale (fleet note)

**Result: R3′ is proved in Lean. The `IsHolChart` atlas is exactly the atlas of Serre's complex space
`(A_τ(ℂ), 𝒪^an)`, and the proof uses T35 only. No new leaf. VERIFIED: compiles, standard axioms.**

```lean
ZInQ.R3Etale.isHolChart_iff_isSerreChart' (hT35 : UniformizationExists) 𝒢 g (hg : A.dim = g) τ φ :
  IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ
ZInQ.R3Etale.isSerreMetricSq_iff (hT35) 𝒢 g hg τ eta r : IsSerreMetricSq 𝒢 τ eta r ↔ IsAnMetricSq 𝒢 τ eta r
```

- **Serre's sheaf.** `AnHolAt` says: near `q`, `h = H(s₁,…,s_m)`, with `s_j` regular functions of `𝒢` and `H`
  holomorphic. This is GAGA §2's sheaf on `𝒢.Pts τ` with `anTop`.
  - It is not built from étale coordinates, so the vendored-atlas circularity the brief warned about does not
    arise.
  - `IsSerreChart` means `φ` is an isomorphism of ringed spaces onto an open subset of `ℂ^g`.
- **New glue proved in Lean.**
  - `translationAnHol`: left translation by a complex point is Serre-holomorphic.
  - Its algebraic core is `exists_tensor_formula`: a section of `X ×_{R₀} Y` is read at `(a, b)` as
    `Σ u c(b) / (Σ v c(b))^N`. The proof uses `pullbackSpecIso` and a basic-open fraction.
  - The analytic half uses r3-residual's T35 tools: `unif_holChart`, `chart_comp_unif`, `holo_in_chart_of_lift`.
- **Not used.** sga1-etale's leaf, sga1-fix's 3.3(a) and the vendored ComplexPoint atlas.
- **The general case.** It is not proved: étale coordinates on an arbitrary smooth ℂ-variety. It would need either
  the IFT plus a bridge from `anTop` to the subspace topology (sga1-fix's 3.3(a)), or Osgood's theorem.
- **ON THE SPOT.** This argument is in neither the manuscript nor its bibliography.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/HolChartSerre.lean`, which imports `AnalyticStableHeight` only. It has no
  warnings.
- The scratch copies `scratch/r3prime-etale/R3Etale.lean` and `THGeneric.lean`.
- `#discharges`: `scratch/r3prime-etale/discharges-output.txt`. No field is discharged, because R3′ was a reading
  step inside the leaves' height predicate, not a field.
- `autofold.json` holds an empty spec plus the proposed flag updates.

**What remains.**
- The lead and reviewer should apply the flag updates in report §5. They drop the R3′ caveat from
  `bostLowerBoundAn(SS)`, `gaudronRemondThm14An(SS)` and `javanpeykarThm111(An)`.
- What remains per row after that:
  - Bost: display, normalization and locator; the row is being re-routed anyway.
  - GR: the statement check of Thm 1.4 and κ.
  - Javanpeykar: the ruling on the composite with §2.3, and the definition-level readings.
- Count-neutral by itself.
- Reading note (STANDARD, not in Lean): regular functions of `𝒢` give the same sheaf as those of `𝒢 ×_τ ℂ`.
  `anTop`'s docstring already makes the same reading.

Report: `docs/research/r3prime-etale.md`.
