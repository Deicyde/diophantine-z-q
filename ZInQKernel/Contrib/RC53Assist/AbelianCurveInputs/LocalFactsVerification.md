# Local differential facts and pointed S2a

## Outcome

**The original S2a input (2), `AbelianCurve.RegularDifferentialComparison`, is proved.**
`LocalFacts.regularDifferentialComparison` has that exact type and no comparison,
trivialization, genus, or Weierstrass hypothesis.

The proved field facts are `LocalUniformizerBasis` and `UniformizerResidueOrder`.
The actual parameterized generic-restriction map is injective, has image exactly
Ω(0), and is natural for actual sheaf pullback and actual Weil cotrace when the
separating parameter is transported by the curve isomorphism.

The rebuilt comparison equals the comparison in
`InvariantDifferential/DivisorZero.lean` by `rfl`. The existing S2c holomorphic
characterization transfers to it.

**Not proved:** `SeparatingCotraceChainRule`, the full intrinsic parameter-free
canonical package, and `InvariantDifferentialTrivialization`.

## Sources

All paths below are relative to
`ZInQKernel/Contrib/RC53Assist/AbelianCurveInputs/`.

- `LocalFacts.lean`: 39,597 bytes; SHA256
  `de0bbf862be7cf4bed501ed42e1c90de85408f7eaa6fce767e1c979998e81363`.
- `LogarithmicNorm.lean`: 8,562 bytes; SHA256
  `17543799c33a304d06093e3657030493a6616235ba80dd15a7907293cff07e6f`.
- `S2aConsequence.lean`: 5,218 bytes; SHA256
  `8485d2d1e8236665f85991dafc9060d5b2a70e6887bcf9de8f39435ab620b33c`.
- `LocalFactsKernelAudit.txt`: 37,696 bytes; SHA256
  `f80fd1d9a61a35907508897410e81842e06f611b702758994e088b77bd6c9157`.

The audit contains the exact types and axiom reports of all 31 explicitly named
new declarations, including all 25 theorems. It also prints the definitions of
the original inputs and the new remaining numerical normalization statement.

## Proved local facts

### Local Kähler basis

```lean
theorem LocalFacts.localUniformizerBasis : LocalUniformizerBasis
```

At a place P, the actual valuation ring is essentially of finite type over the
constant field: normalize a polynomial subring in the finite separable function
field, then localize at the center of P. Its residue field is finite and
separable over the constants.

For an essentially finite-type local algebra A with separable algebraic residue
field, differentiate a residue minimal polynomial. Its derivative is a unit,
and the polynomial value is a multiple of a uniformizer t. Every Kähler
generator therefore belongs to the span of dt plus the maximal ideal times the
Kähler module. Finiteness and Nakayama imply generation by dt. Localization into
the rational Kähler line proves independence.

The result is proved for every uniformizer, not just a selected generator.

### Normalized order of dt

```lean
theorem LocalFacts.uniformizerResidueOrder : UniformizerResidueOrder
```

The local basis proves that differentiation with respect to a uniformizer
preserves the valuation ring. In characteristic zero, a positive-order function
has derivative order exactly one less. Tameness gives e = d + 1. The actual
cotrace divisor formula then computes the order of the separating differential
as the order of the uniformizer-coordinate derivative. The reciprocal Kähler
coordinate derivative cancels this order, giving ord_P(comparison(dt)) = 0.

This proof does not use the Weil parameter-change chain rule.

## Comparison bridge and S2c

```lean
theorem LocalFacts.comparison_eq_divisorZero :
  AbelianCurveInputs.comparison hF hex hx =
    InvariantDifferential.comparison hF hex hx
```

The complete binders and local module instance are printed in the audit. The
proof is `rfl`, so there is no unidentified scalar or normalization change.

`LocalFacts.comparison_mem_holomorphic_iff` transfers the existing theorem:
for a nonsingular affine Weierstrass curve, the comparison image of a rational
Kähler differential lies in Ω(0) exactly when that differential is a unique
constant multiple of the actual invariant Kähler differential.

The unconditional sheaf consequences are:

```lean
theorem LocalFacts.regularDifferentialComparison :
  AbelianCurve.RegularDifferentialComparison

theorem LocalFacts.regularDifferentialComparisonParameterized :
  RegularDifferentialComparisonParameterized
```

The second theorem includes the actual map, injectivity, exact image, and
naturality with transported parameter. It is not merely an equality of dimensions.

## Remaining parameter normalization

`LocalFacts.comparisons_differ_by_constant` proves that comparisons built from
any two separating parameters differ by a unique nonzero constant in the exact
constant field. It does **not** prove that the constant is 1.

The precise unproved numerical statement is:

```lean
def LocalFacts.LocalLogarithmicNormalization : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (x : F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) (t : F) (_ht : P.valuation.IsUniformizer t),
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F t) :
      Module.Dual k ↥(repartitionSpace k F)) P t⁻¹ = (P.degree : k)
```

This is one logarithmic residue evaluation, not a statement about global section
spaces. It is a defined proposition, not an axiom or a proved fact.

The following reduction is proved:

```lean
theorem LocalFacts.separatingCotraceChainRule_of_logarithmicNormalization
    (hN : LocalFacts.LocalLogarithmicNormalization) :
    SeparatingCotraceChainRule
```

A comparison ratio is a constant c. Evaluating both maps on dt/t at one place
would give c · degree(P) = degree(P). Characteristic zero and positive degree
force c = 1, yielding the chain rule.

An auxiliary standard field identity is also proved in `LogarithmicNorm.lean`:

```text
Tr_{F/k(x)}(δ_x(z)/z) = δ_X(N_{F/k(x)}(z))/N_{F/k(x)}(z),  z ≠ 0.
```

The exact rational-function-algebra structure and all binders are in the audit
under `separating_trace_logarithmic_derivative`. The proof differentiates the
product over embeddings and uses the corresponding sum formula for trace.
No Weil parameter-independence fact is assumed.

The norm identity does not finish the local residue evaluation. The remaining
route needs the valuation-of-norm fiber calculation and the rational normalized
logarithmic residue computation. No theorem claiming either calculation has
been supplied here.

## Strongest pointed S2a consequence

`S2aConsequence.lean` removes input (2) from the existing pointed projective-model
conclusions. Each of these theorems takes only
`AbelianCurve.InvariantDifferentialTrivialization` as an original mathematical input:

- `abelian_isEllipticFunctionField_of_trivialization`;
- `abelian_projectiveWeierstrassModel_of_trivialization`;
- `abVar_projectiveWeierstrassModel_of_trivialization`, for the actual `PkgI3.AbVar`;
- `groupAbVar_projectiveWeierstrassModel_of_trivialization`, for the actual
  `PkgI2.IsAbelianVariety` presentation.

The projective-model conclusions retain the rational base square, the specified
function-field pullback, and identity mapped to the actual projective point at
infinity. They are still conditional on the invariant sheaf trivialization.
The group translation, smoothness, and affine Hopf-algebra interfaces were
inspected, but no proof of the remaining sheaf trivialization was constructed.
No replacement genus or Weierstrass assumption was introduced.

## Verification and custody

- Lean 4.35.0; six threads; `maxHeartbeats 800000`.
- All three new source files pass individual, actual import-based Lean checks,
  with no warnings. No whole-project build was run.
- The normal build tree lacked `RegularComparison.olean`. A byte-identical copy
  of the frozen source was compiled as its original module in the separate
  `VerificationCache/`. Required dependency objects were copied from an explicit
  source-import manifest. No existing source or compiled object was changed.
- The frozen comparison source has 161,698 bytes and SHA256
  `a4196f648a7290bfeef96e60bc1f6354d23cb90b1e545db8477f7bad5b180256`.
  Its five existing unused-variable warnings were unchanged.
- The new type-and-axiom audit exits successfully with 31 reports and empty stderr.
  Its seven logarithmic-norm declarations are exposed by a byte-identical source
  block to make the private names available in the audit; the other 24 declarations
  are checked through their actual compiled imports. The standalone logarithmic
  norm source was separately checked through actual imports as well.
- Every declaration's reported axiom set is exactly
  `{propext, Classical.choice, Quot.sound}`. There are no additional axioms.
- All 31 named declarations have kind-and-locator docstrings. The three proof
  files contain no prohibited proof or declaration commands, no broad Mathlib
  import, and no private runtime identifiers or external working paths.
- The pre-existing `RegularComparison.lean`, `KernelAudit.txt`, `Verification.md`,
  and `Manifest.json` retain their original hashes. No Git operation, commit,
  subagent, human outreach, or memory write was performed.
