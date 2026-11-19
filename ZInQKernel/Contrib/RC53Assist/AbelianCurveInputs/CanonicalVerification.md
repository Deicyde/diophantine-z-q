# Parameter independence and the complex algebraic differential line

## Outcome

**`SeparatingCotraceChainRule` is proved.** The reduced local logarithmic residue
normalization is also proved outright, and the full
`RegularDifferentialComparisonCanonical` record is now closed. None of these
three theorems takes a residue-normalization, chain-rule, global-comparison,
genus, or Weierstrass-model proposition as a hypothesis.

```lean
theorem CanonicalResidues.localLogarithmicNormalization :
  LocalFacts.LocalLogarithmicNormalization

theorem CanonicalResidues.separatingCotraceChainRule :
  SeparatingCotraceChainRule

theorem CanonicalResidues.regularDifferentialComparisonCanonical :
  RegularDifferentialComparisonCanonical
```

The closed canonical record retains the actual global-section restriction to
the generic stalk, its Kähler identification, the normalized Weil comparison,
injectivity, exact image Ω(0), agreement with every separating parameter, and
parameter-free naturality for actual sheaf pullback and actual field cotrace.

The algebraic complex differential-line statements are proved as well:

- For every nonsingular Weierstrass curve over the complex numbers, its actual
  regular Kähler submodule is exactly the complex span of
  `dx / (2y + a₁x + a₃)`.
- Its actual holomorphic Weil filtration is the complex span of the comparison
  image of that invariant form, for every separating parameter.
- Scalar extension of the actual rational global differential-sheaf sections
  is canonically equivalent to scalar extension of their regular Weil image.
  The map on pure tensors is the actual intrinsic generic restriction, and it
  is natural for the actual sheaf differential pullback and Weil cotrace.

**The literal analytic Shimura `D_A = ℂ ω_A` identification is not claimed.**
The realization of `D_A`, the comparison with the actual differential sheaf on
the complex base-changed scheme, and analytification/GAGA compatibility remain
unproved here. The original `InvariantDifferentialTrivialization` input also
remains unproved.

## New sources and custody

All paths below are relative to
`ZInQKernel/Contrib/RC53Assist/AbelianCurveInputs/`.

| Source | Bytes / lines | SHA256 |
|---|---:|---|
| `ResidueNormalization.lean` | 13,841 / 274 | `23f49d754298ee786fa5f78bf8c58ce2c65854d4952b7a4d27d2f3a696d3c6ce` |
| `RationalResidues.lean` | 17,242 / 336 | `043a3b35cdbc12e727748c166f19ff33bdf0b5b9d766585e4a20ecf0b5945664` |
| `TraceSelector.lean` | 6,652 / 131 | `0be947e0348ff91fb90270dc76711ac74d815d86039d2240dcfd42207e44c820` |
| `CanonicalResidues.lean` | 16,467 / 294 | `d0ce3fcdf1c6cd8ccea3d4aaef046494dadda9f13e8a85dbe0faea8bbe24974b` |
| `ComplexDifferentialLine.lean` | 16,463 / 316 | `7a93daacf2adfa26c2ec0410d353cf8dd25f5707584d6ac7a67656b6ec5e2c59` |
| `NormalizedExamples.lean` | 4,595 / 84 | `884515dd3f7d2892b6d0b784cb51254ff54af42552d904fc5ff268dd860aa417` |

There are 43 explicitly named declarations, including 39 theorems. Every
one has a kind-and-locator docstring. The six proof files contain no prohibited
proof commands, new axioms, syntax declarations, broad Mathlib import, private
runtime identifiers, or external working paths. All heartbeat limits are at
most 800,000.

The previously published `RegularComparison.lean`, `LocalFacts.lean`,
`LogarithmicNorm.lean`, and `S2aConsequence.lean` retain their original hashes.
No existing source was modified. No Git operation, commit, subagent, human
outreach, or memory write was performed.

## The local normalization proof

The exact reduced numerical fact is now proved:

```lean
theorem uniformizer_logarithmic_normalization
    {k F : Type} [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) {t : F} (ht : P.valuation.IsUniformizer t) :
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F t) :
      Module.Dual k ↥(repartitionSpace k F)) P t⁻¹ = (P.degree : k)
```

The proof uses residual trace rather than a valuation-of-norm theorem:

1. **Local logarithmic rule.** For a functional annihilating the actual valuation
   ring, uniformizer-coordinate differentiation gives
   `ell(δ_t(s)/s) = ord_P(s) · ell(t⁻¹)`. This follows from writing
   `s = t^n u`, where u is a unit, and the already proved preservation of the
   valuation ring under `δ_t`. The comparison logarithmic form therefore kills
   the local maximal ideal.
2. **Rational logarithmic residues.** At infinity, the normalization on X inverse
   and the uniformizer X inverse give residue `ord_∞(s)`. For a finite place of
   an irreducible polynomial q, the abstract residue theorem applied to q'/q
   has support only at that place and infinity. The finite residue is
   `q.natDegree`, which is the place degree. The local logarithmic rule gives
   the general formula `ord_Q(s) · degree(Q)` at every rational-function place.
3. **Residual trace selector.** Normalize the base valuation ring in the finite
   separable field extension. Its mapped maximal ideal has a factorization
   `P^e · J` with coprime factors. A Chinese remainder lift b is one modulo P
   and zero at all other residue primes in the fiber. The trace of the quotient
   by P^e is e times its residue-field trace, so the field trace of b is
   congruent to `e · f` modulo the base maximal ideal.
4. **Actual cotrace.** Evaluate the trace-pairing identity on a fiber-constant
   repartition using b and a base uniformizer logarithm. All other local
   components vanish; b minus one is also killed at the chosen place. The
   rational residue calculation gives `e · f · degree(Q) = e · degree(P)`.
5. **Cancellation.** The local logarithmic rule gives the same value as e times
   the target uniformizer logarithmic residue. Characteristic zero and the
   positive ramification index cancel e, proving the asserted degree(P).

The normalized rational source is definitionally reconciled with the source
of the existing separating cotrace; there is no unexplained scalar change.
The earlier logarithmic norm–trace theorem is not needed in this residual-trace
route and was not modified.

The previously proved constant-ratio argument then forces the ratio between
any two separating-parameter comparisons to be one. This closes the full
chain rule and canonical comparison.

## Field and curve naturality

`CanonicalResidues.comparison_fieldTransport_parameter_free` proves the actual
Kähler/Weil transport square with arbitrary separating parameters on both sides:

```text
comparison_y(kaehlerFieldTransport(σ, η))
  = weilFieldTransport(σ, comparison_x(η)).
```

The exact field binders, function-field and exact-constant hypotheses, and
scalar instances are printed in the audit. Both transports are the original
universal-derivation and actual cotrace constructions, not maps manufactured
by conjugating chosen vector-space equivalences.

The closed `RegularDifferentialComparisonCanonical.naturality` field supplies
the corresponding actual sheaf pullback square for proper smooth geometrically
integral rational curves, with no parameter in its statement.

## Complex algebraic statements

`ComplexDifferentialLine.regularKaehlerSubmodule W` is defined as the preimage
of the actual zero-divisor Weil filtration under the normalized comparison.
It is not chosen to have dimension one. The closed parameter-independence
result proves agreement with every separating-parameter construction.

The explicit complex formula is:

```lean
theorem complex_regularKaehler_explicit_formula
    (W : WeierstrassCurve.Affine ℂ) [W.IsElliptic] :
    regularKaehlerSubmodule W = Submodule.span ℂ
      {(2 * W.genericY + algebraMap ℂ W.FunctionField W.a₁ * W.genericX +
          algebraMap ℂ W.FunctionField W.a₃)⁻¹ • D ℂ W.FunctionField W.genericX}
```

`comparison_mem_holomorphic_iff_parameter_free` says that a rational Kähler
form has holomorphic comparison image precisely when it is a unique constant
multiple of the actual invariant form. It holds over every characteristic-zero
constant field in the stated universe, and hence over the complex numbers.

`complex_holomorphicWeil_eq_span_comparison` identifies the actual complex Weil
filtration with the complex span of that comparison image for every separating
parameter. Thus the algebraic function-field `ℂ ω` assertion is proved, not
merely its dimension.

For an actual smooth proper geometrically integral rational curve X of
Krull dimension one, `canonicalRegularSectionEquiv` is the actual intrinsic
comparison restricted to its regular image. Its complex scalar extension is:

```text
ℂ ⊗[ℚ] Γ(Ω_{X/ℚ}, ⊤)
  ≃ₗ[ℂ] ℂ ⊗[ℚ] holomorphicWeilSubmodule(ℚ, X.functionField).
```

`complexifiedCanonicalRegularSectionEquiv_tmul` identifies its pure-tensor map
with `c ⊗ s ↦ c ⊗ intrinsicWeilComparison(s)`, after the natural inclusion of
the regular target. `complexified_intrinsic_naturality` proves its compatibility
with scalar extension of the actual sheaf differential pullback and actual
Weil cotrace under curve isomorphisms.

The scalar-extension span theorem is also proved for any characteristic-zero
constant field embedded in the complex numbers. These tensor-product statements
are deliberately not labeled as the analytic Shimura `D_A`.

## Exact remaining items

1. **Invariant sheaf input.** `AbelianCurve.InvariantDifferentialTrivialization`
   remains unproved. The previously delivered pointed S2a consequences still
   take that original input. This continuation does not add a genus or
   Weierstrass-model assumption to replace it.
2. **Actual complex-scheme base change.** No proof is supplied here identifying
   `Γ(Ω_{X_ℂ/ℂ}, ⊤)` with `ℂ ⊗[ℚ] Γ(Ω_{X/ℚ}, ⊤)`, including compatibility of
   their actual generic restrictions and invariant forms. The scalar-extension
   equivalence above is not silently substituted for this assertion.
3. **Analytic realization.** No proof is supplied identifying Shimura's analytic
   holomorphic differential space `D_A` with the algebraic global-section space
   of the actual complex curve, with analytification/GAGA and the distinguished
   Weierstrass form compatible. The original S2 reference states a reading
   translation and does not itself define a separate Lean `D_A` object.

There is no remaining local residue-normalization or chain-rule input. The
parameter-independent canonical algebraic comparison is unconditional under
its stated curve hypotheses.

## Verification and exact statements

All six source files compile individually through actual imports, using Lean
4.35.0, six threads, and `maxHeartbeats 800000`. Only single-file Lean commands
were used. The isolated verification cache is under the permitted new-file
directory; no existing source or build object was changed.

There are three nonblocking diagnostics: a deprecated `SetLike` lemma in
`ResidueNormalization`, an unused `change` in `RationalResidues`, and a deprecated
tensor-induction alias in `ComplexDifferentialLine`. None is a proof hole.

- `CanonicalFreshAudit.txt`: 13 exact type/axiom reports from a fresh elaboration
  of the complete byte-identical `CanonicalResidues.lean` source prefix.
- `CanonicalImportedAudit.txt`: 37 exact type/axiom reports through actual
  compiled imports, plus three independently retyped closed-target examples
  and prints of the original local-normalization, chain-rule, and canonical
  record definitions.
- The union covers every one of the 43 named declarations, including all
  39 theorem statements. The seven public canonical declarations intentionally
  appear in both audits.
- Every reported axiom set is exactly
  `{propext, Classical.choice, Quot.sound}`. Both audits exit zero with empty
  stderr and no nonstandard axiom.
- `CanonicalFreshAuditRecipe.txt` and `CanonicalImportedAuditRecipe.txt`
  preserve the precise scratch source used for those checks. The executable
  scratch `.lean` files are not integration sources.
- `NormalizedExamples.lean` checks X and X inverse in the actual rational
  function field over the complex numbers. It proves the nontrivial inverse
  chain rule, equality of the independently constructed comparisons, and
  logarithmic uniformizer residue one, exhibiting a nonzero local functional.

Audit custody:

```text
CanonicalFreshAudit.txt — 8,495 bytes
SHA256 35abf73dbd9d2e566965cf4479eb58903709cf653dfeb5032026213dace481bb

CanonicalImportedAudit.txt — 41,256 bytes
SHA256 a006e2d80ee29695764b3e1e0bba04c8319438dbfc501347ba9ef218ff1fcaeb

CanonicalFreshAuditRecipe.txt — 19,098 bytes
SHA256 c2c36e49aa8ac6112e163ea6b9106951cd855f2402492db0fdc26fea652639ab

CanonicalImportedAuditRecipe.txt — 8,948 bytes
SHA256 a9e28137bf380ae3fa3d822ca9e7066151a900aaaf4bfe9b312cb92928df3b64
```
