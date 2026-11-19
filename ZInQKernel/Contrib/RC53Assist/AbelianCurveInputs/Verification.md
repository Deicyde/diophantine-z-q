# Canonical regular-differential comparison

## Result and scope

Input (2), `AbelianCurve.RegularDifferentialComparison`, is **reduced, not unconditionally discharged**. The stronger `RegularDifferentialComparisonCanonical` retains an intrinsic map, its exact regular image, independence of the separating parameter, and naturality for actual isomorphisms of rational curves.

The map is global sheaf sections → the actual generic differential stalk → rational Kähler differentials → normalized cotrace Weil differentials. Neither the map nor the sheaf pullback is defined by an equality of dimensions or a chosen global differential generator.

The following parts are proved:

- The stalk of the actual sheafified relative differential sheaf is canonically the Kähler module of the actual local ring, with the universal derivative preserved. Smoothness is not needed for this stalk calculation.
- Generic restriction, its injectivity once the local Kähler maps are injective, and unique global gluing from membership in every local stalk.
- Every place of the actual function field of a smooth proper rational curve is represented by a discrete local ring on that curve.
- Regularity at a place is the nonnegative-order condition for a nonzero Weil differential, with the zero differential handled separately.
- The actual sheaf differential pullback, its generic-stalk and rational Kähler compatibility, and the normalized comparison's naturality when the separating parameter is transported by a curve isomorphism.
- Under the local basis fact, the actual global differential pullbacks of a curve isomorphism and its inverse are inverse rational-linear maps.
- The canonical form implies the existing existence-of-linear-equivalence form by restricting the actual map to its image.

The global scheme statements are over ℚ, as in the original input. Field-transport statements also cover characteristic-zero constant fields. No assertion that S2a is finished, or that `D_A = ℂ ω_A`, is made.

## Main exact statement

All names below are in `ZInQ.Contrib.RC53Assist.AbelianCurveInputs`.

```lean
theorem regularDifferentialComparisonCanonical_of_local_inputs
    (hB : LocalUniformizerBasis)
    (hO : UniformizerResidueOrder)
    (hP : SeparatingCotraceChainRule) :
    RegularDifferentialComparisonCanonical
```

`RegularDifferentialComparisonCanonical` has three fields: `image`, `parameter_agreement`, and `naturality`. Its fixed map is `intrinsicWeilComparison`. The regular image is `holomorphicWeilSubmodule`, the inverse image of `TauCeti.weilDifferentialFiltration 0` under the inclusion of Weil differentials into repartition linear forms.

The naturality equation uses `globalDifferentialPullback` on sheaf sections and `weilFieldTransport` on Weil differentials. The latter is the actual cotrace of the field isomorphism induced by the curve isomorphism. The map `globalDifferentialPullbackEquiv` is proved to have exactly the actual sheaf pullback as its forward map.

## Precisely what remains

No remaining fact mentions global sheaf sections, a holomorphic dimension, genus one, or a Weierstrass conclusion.

### 1. Valuation-ring uniformizer basis

```lean
def LocalUniformizerBasis : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (_hF : IsFunctionField k F) (P : Place k F),
    ∃ t : P.integers, P.valuation.IsUniformizer (t : F) ∧
      ∃ b : Basis Unit P.integers (KaehlerDifferential k P.integers),
        b () = D k P.integers t
```

This says that the actual local Kähler module is free on `dt`, not that a global differential space has rank one.

### 2. Normalized uniformizer differential has order zero

```lean
def UniformizerResidueOrder : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (x : F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) (t : F) (ht : P.valuation.IsUniformizer t),
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOrder hF hex (comparison hF hex hx (D k F t)).2
      (comparison_uniformizer_ne_zero hF hex hx P ht) P = 0
```

Nonvanishing in this statement is already proved. Together with the local basis, this single local order identity proves exact local image equality and then exact global image equality with Ω(0).

### 3. Normalized cotrace chain rule

```lean
def SeparatingCotraceChainRule : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (_hex : IsIntegrallyClosedIn k F) (x y : F)
    (hx : Transcendental k x) (hy : Transcendental k y),
    letI := hF.finiteDimensional_adjoin hx
    letI := hF.finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule hF
    differentialOfSeparating hF hy =
      derivativeOfSeparating hx y • differentialOfSeparating hF hx
```

This fact is needed only to prove parameter independence and parameter-free naturality. Naturality with the parameter transported by the actual field isomorphism is already proved without it.

The separate input (1), `InvariantDifferentialTrivialization`, remains unproved and unchanged.

Locators: Silverman, Chapter II, §§4–5; Stichtenoth, §§I.5 and I.7 and Proposition III.4.11 for the repartition/cotrace formulation. Stichtenoth is an auxiliary reference, not a manuscript citation.

## Comparison normalization and integration limit

The normalized comparison construction is reproduced from `InvariantDifferential/DivisorZero.lean`: `dX` has divisor `-2[∞]` and the value `-1` on `X⁻¹` at infinity, and separating differentials are its cotrace. The original module's compiled object is absent from the supplied build tree. No existing file was rebuilt or changed.

`comparison_unique_of_D_self` proves that an implementation is determined by its image of `dx` under this normalization. Direct cross-module equality with the original S2c comparison declaration was not checked here because its compiled object is unavailable.

## Verification

`RegularComparison.lean` passed the requested individual-file Lean check. `KernelAudit.txt` records every named declaration's exact Lean type and its scratch `#print axioms` result: 149 declarations, including all 92 named theorems, were audited. The audit prefix was byte-identical to the final source.

Every dependency is one of the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; there are no additional axioms. The five compiler warnings concern unused section typeclass hypotheses only.

Static checks found no prohibited proof or metaprogramming constructs, no whole-Mathlib import, no private runtime identifiers or absolute paths in the source, and no missing kind-and-locator docstrings. The source uses `maxHeartbeats = 800000`. Checks used six threads and the requested CPU affinity and priority.

### Files

- `ZInQKernel/Contrib/RC53Assist/AbelianCurveInputs/RegularComparison.lean`
  - Size: 161698 bytes; 3072 lines.
  - SHA256: `a4196f648a7290bfeef96e60bc1f6354d23cb90b1e545db8477f7bad5b180256`.
- `ZInQKernel/Contrib/RC53Assist/AbelianCurveInputs/KernelAudit.txt`
  - Size: 168152 bytes.
  - SHA256: `05d94018a0508e8ee6dc4727ba3f40d73d4a573b4477583db9801ae1a0e6626a`.

The exact source and complete audit accompany this report. No commits, checkouts, project builds, memory writes, or human outreach were performed.
