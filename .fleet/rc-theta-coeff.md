# Theta coefficient handoff

Result commit: `929bd91bddd5fa8a739961b74289f67cc95ef6e0` on `wip/rc-theta-coeff`.

For an actual theta stage with the chosen `P_M` as a parameter, and a fixed finite pool of good primes, `RC/ThetaCoeff` constructs the exact integral expansions of `B_U`, `H_U`, and `F_U = θH_U`. It supplies the constituent Fourier coefficients and their continuity, the good Hecke and diamond operators, and the determinant Fourier data. The good formula covers degeneracy translates and Eisenstein divisor sums. The integral module includes both Hecke and diamond translates; integrality alone would not establish stability of the diamond span (tex 9660–9668).

The call to `buildConstituentModel` compiles, with `hdiam`, `read`, and `h2fresh` still hypotheses. The checked obstruction is that its stationary support must contain every avoided prime, including the added level primes, even though their bits are independent of the stationary type. This forces the pool to be empty. For nonempty pools, use the manuscript’s formwise inertia at tex 9745–9750 with the checked lemma `Blocks.inertia_le_consN_of_seed`. The level assignment on the nonzero constituents still needs to be supplied. The weight-two realization at tex 9647–9654 is ELLIOT (uncited). No new print was added.

All six Lean files compiled individually; 72 axiom audits passed. Details: `docs/research/rc-theta-coeff.md`. Verification log: `scratch/rc-theta-coeff/log.md`. The final handoff commit SHA is given by `git log -1 --format=%H -- .fleet/rc-theta-coeff.md`.
