# Appendix E: half-integral weight twist

`HalfIntegral.halfIntegralTwist` proves `AppE.HalfIntegralTwist` exactly
at level `N³`. It gives the twist of character `ψν²` with coefficients
`ν(n)a_f(n)`, and the level has precisely the original prime support.
`HalfIntegral.evenPhaseData_Ecurve` applies the existing Appendix E
assembly with `hTw` discharged.

The theta ratio comparison uses Poisson summation at positive denominators,
a change of variables in the resulting quadratic sum, and the symmetry
under negation for negative denominators. The comparison needs
`4m² ∣ c`; membership of the two conjugate matrices in `Γ₀(4)` by
itself is insufficient. At the primitive conductor the Fourier weights
recover the normalized Gauss sum. At the original modulus they also
delete coefficients on nonunits.

All nine new Lean files compile with `lake env lean`. Each of the 42
theorem axiom checks reports only `propext`, `Classical.choice`, and
`Quot.sound`. No new printed-form leaf was introduced. Nothing remains
for this GLUE step; the other hypotheses of Appendix E's phase data
theorem are retained.

Report: `docs/research/rc-hiw-twist.md`. Results log:
`scratch/rc-hiw-twist/log.md`.

Proof and report commit: `adf77c55fc479033b9e1481a652197d91dbb0e9c`. The final handoff commit is
identified by `git log -1 --format=%H -- .fleet/rc-hiw-twist.md`.
