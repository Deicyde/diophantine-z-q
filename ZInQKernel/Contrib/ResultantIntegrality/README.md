# Integer reflection from polynomial resultants

`PrivateResultantIntegrality.integerPolynomial_of_integral_resultants` proves:

- `χ : ℚ[X]` is monic;
- for **every** integer polynomial `R` with `R.natDegree ≤ χ.natDegree`, the default-degree resultant of `χ` and `R.map (Int.castRingHom ℚ)` is an integer;
- therefore one monic `F : ℤ[X]` maps to `χ`.

The test polynomial need not be monic. The boundary is included, and the degree-zero case is retained. Clearing-denominator minimality, nonzero reduction modulo a denominator prime, and the constant/positive reduced-degree branches are proved internally.

This is a generic algebraic supplier. It does **not** prove the abelian-variety integer-characteristic-polynomial leaf or Hilbert 10: the actual endomorphism's all-resultant input and its characteristic-polynomial comparison remain separate consumer obligations.

## Tests

The accompanying modules include genuine integer-resultant inputs; the monic literals `1`, `X`, `X²−2`, and repeated `X²`; explicit nonintegral resultant witnesses `+1/2`, `+1/2`, and `−1/3`; counterexamples to strict degree bounds and dropped input monicity; and both modular reduced-degree branches.

`ResultantIntegralitySuiteExpected.lean` imports only Mathlib and stores independent proposition values. The cases apply the actual reflection theorem to proved inputs, not a caller-provided intended integer lift.

`ResultantIntegralitySuiteKernelChecks.lean` checks 13 complete actual theorem types against those values, the actual stored proof bodies, LP[] fresh checking-additions and annotation-sensitive readbacks. It runs 13 extra-premise comparisons, 13 corrupt-body rejection controls, four wrong-contract/unchanged-body controls, and 26 type/available-opaque-value dependency walks. Its validation import is explicitly trust level zero. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

All eight modules were freshly compiled on Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and the unchanged Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`. The complete selected checker succeeded with all 13 completion records, 26 closure records and four wrong-contract records. Original style/deprecation warnings are retained rather than suppressed.

Reproduce the check with:

```sh
lake build +ZInQKernel.Contrib.ResultantIntegrality.Basic
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityPositiveCases
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityAdverseCases
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityContractCounterexamples
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityReductionBranches
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteExpected
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases
lake build +ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteKernelChecks
```

These checks do not replay every imported library declaration or serialized recursor-rule RHS. `Expr.equal` compares stored expressions, not serialization bytes; outer binder diagnostics are not a whole-expression annotation algorithm. `addDeclCore 200000000 20000` specifies heartbeat/recursion limits, not trust settings. Hosted CI and full-project integration are separate from these local selected checks.

## Provenance and compatibility

AI tools assisted proof construction and independent source review. Public packaging preserves the mathematical declarations and executable proof lines; only private comments, import paths and literal defining-module references were adapted. The historical `PrivateResultantIntegrality` declaration namespace is retained for existing-consumer compatibility—it does not make the exported theorem inaccessible.

No project target, Objects file, pin, root configuration, existing AVB1/FrobChain proof or assembly is changed. The earlier proof-development import failure is retained in the private evidence record; it was resolved by fetching the exact already-pinned Mathlib cache module, not by changing a proof or dependency revision.
