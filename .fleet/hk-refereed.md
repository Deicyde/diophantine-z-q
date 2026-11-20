# Kolyvagin input: stage-one handoff

**Verdict.** The pole proof needs one infinite-order point in `E_ℓ(ℚ)` when
`ℓ > 0` is squarefree, `ℓ ≡ 11 (mod 12)`, the explicit 2-Selmer group has
eight classes, and the modular curve has analytic rank one. The old `hK`
supplies this via its rank projection. Kummer counting supplies surjectivity,
so the proof does not need the rank upper bound or finiteness of Sha.

**VERIFIED (Lean).** `hkConsumed_of_hK`, `poleCompleteness_of_hkConsumed`,
the drafts' shared conditional implication, and the scratch headline
substitution compile with only `propext`, `Classical.choice`, and
`Quot.sound`. The scratch check uses the actual BCDT adapter and final
assembly, with the unchanged height supplier passed as a parameter. No
existing statement or integration file changed.

**Reading remains open.** Both candidate locators are **UNVERIFIED**. Check
the arithmetic rank theorem in the Festschrift chapter and Gross's Durham
chapter against the concrete trace premise. The drafts require a non-torsion
trace over an imaginary quadratic field, which modularity alone does not
provide. The application still needs `PoleNonTorsionHeegnerTrace` and the
rational-line comparison `PoleHeegnerRankDescent` (or equivalent
orientation). The paper-to-Lean parametrization dictionary also needs
checking. The preprint remains GLUE; no mathematical error was found in
the checked rank-one manuscript steps. See `docs/research/hk-refereed.md`
for the page checks. Stop here for the reading.
