# r3prime-bc (fleet note)

**Result: the lead's condition (ii) is proved, so R3′ holds with no reading note. VERIFIED: compiles, standard axioms only.** The
`IsHolChart` atlas is the atlas of Serre's complex space of the `ℂ`-scheme `𝒢 ×_{𝓞_L,τ} Spec ℂ`:
- the points are `CPt` with Bridge's `classicalTopology`;
- the sheaf comes from the base change's own regular functions.

The only hypothesis is T35. There is no new leaf.

```lean
ZInQ.R3BC.isHolChart_iff_isBCSerreChart 𝒢 τ (hT35) g hg φ :
  IsHolChart 𝒢 τ φ ↔ IsBCSerreChart (bc 𝒢 τ) (pushChart 𝒢 τ φ)
```

- **(1) Homeomorphism.** `ptsHomeomorph : (𝒢.Pts τ, anTop) ≃ₜ (CPt (bc 𝒢 τ), classicalTopology)`.
  - It respects evaluation: `xevalAt_toBC`.
  - The topologies agree: `anTop_eq_induced`.
  - `ptsHomeomorphPort` lands in the vendored port's `Point ℂ`, and `chartedSpacePts` transports the vendored atlas.
- **(2) Sheaf comparison.** `bcHolAt_iff : BCHolAt (bc 𝒢 τ) k (toBC q) ↔ AnHolAt 𝒢 τ (k ∘ toBC) q`.
  - The key step is `bc_formula`: near each point, a regular function of the base change is `Σ u_j c_j / (Σ v_j c_j)^N` with `c_j` regular on `𝒢`.
  - It is r3prime-etale's `exists_tensor_formula` with `X = Spec ℂ`.
- **(3) Unit-germ charts.** Results: `bcHolAt_chartAt`, `unitGermChart_bc` and `exists_bcSerreChart_at`.
- **(4) Restatement.** The theorem above, plus `isBCSerreChart_iff_isHolChart` for charts given on the base change.
- **ON THE SPOT.** This identification is not in the manuscript. No manuscript step is involved.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/HolChartBC.lean`, which imports `HolChartSerre` and `CloudB3W17Hodge.Bridge`. It has no warnings.
- The scratch copy `scratch/r3prime-bc/R3BC.lean`.
- `lake build` of Main, Discharges and HolChartBC succeeds (16217 jobs).
- `#discharges`: `scratch/r3prime-bc/discharges-output.txt` has 19 lines, all pre-existing. None is by `ZInQ.R3BC`, because R3′ is not a field.

**What remains.**
- Nothing for R3′.
- The lead should apply the flag updates in `scratch/r3prime-bc/autofold.json`. They supersede r3prime-etale §5: the R3′ caveat drops with no reading note.
- Count-neutral. It folds together with r3prime-etale.

Report: `docs/research/r3prime-bc.md`.
