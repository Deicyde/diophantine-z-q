# period-map (fleet note)

**Result.** All three targets from fibre-qm-period (`PeriodMapGlue`, `HauptmodulUnique`, `QMDenZeroCM3`)
are true as stated (model review) and are proved in Lean from strictly smaller named Props, with no
statement changed, no `sorry`, standard axioms only. Report: `docs/research/period-map.md`; Lean and
log: `scratch/period-map/`.

- `HauptmodulUnique ⇐ S8Nonzero (numeric glue) + SphereFactorAffine (textbook complex analysis)`.
- `QMDenZeroCM3 ⇐ S8Nonzero + S8WeightExact (glue: exact weight-8 automorphy of Σθ⁸∘Ω/dF⁴ on Γ*,
  multiplier 1, verified numerically on 7 elements incl. Atkin–Lehner and elliptic generators)
  + ValenceBoundGammaStar (LEAF: valence formula + signature (0;2,4,6))`.
- `PeriodMapGlue ⇐ R1fp naturality + BaseChangeClassUnique + PiTwistC + QMTwistLattice + PiCMC +
  CMFixedHasCM`; `CMFixedHasCM` is proved from T11a, and `PiCMC` from the leaf candidate
  `CMDescends` (CM objects descend to ℚ̄) with R2fp.
- Proved along the way: Ω(τ) ∈ Siegel space (closed form), holomorphy of the genus-2 theta
  constants along Ω, holomorphy of QMHauptmodul's f into P¹, the three CM points, the double zero
  of Σθ⁸∘Ω at i√3 from the exact automorphy.
- End to end: `fibreQMPeriod_periodMap` (fibre-qm-period's main theorem with the three targets
  replaced by their pieces).

**Compiles (VERIFIED).** `PMLight.lean` (Mathlib only): 0 errors, 17 axioms lines standard.
Single-file `build_full.sh` (fibre-qm-period base + all parts, `lake env lean`): 0 errors, 3m13s,
69 axioms lines, none with `sorryAx`.

**Findings.** fibre-qm-period's report names the weight-8 form `S·dF⁴`; it is `S/dF⁴`. Its committed
`FibreQM.lean` is stale (lacks `fibreQMPeriod_main`). r1b-state's `R01b_ComplexUniformization'` is the
published shape of R1(b) and should replace `R1bFamily` (a bridge of uniformization predicates is
needed; not compiled across the two AbVar layers).

**Remains.** Glue: `S8Nonzero` (certified theta evaluation), `S8WeightExact` (modular embedding +
Igusa, generation of Γ*), `SphereFactorAffine`, `BaseChangeClassUnique`, `PiTwistC`,
`QMTwistLattice`. Leaves for human check: `ValenceBoundGammaStar`, `CMDescends`.
