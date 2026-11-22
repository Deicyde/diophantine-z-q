# Weierstrass models and invariant differentials

## Result

**S2b over `ℚ` and the function-field statement of S2c are proved. S2a remains a scheme-level translation.** No printed theorem is a Lean hypothesis in the two proof files.

The supplied integration base is `3b0ffbb9`. The original `ModularWeil/DifferentialLine.lean` is unchanged. It already proved the dimension of holomorphic Weil differentials and the function-field span of the Kähler invariant differential; the new files supply the missing divisor computation and the forward Weierstrass-model construction.

- `DivisorZero.lean`: normalized Kähler–Weil comparison; divisor and order zero for `dx/(2y + a₁x + a₃)`; the holomorphic line over the constant field; the corresponding criterion for Kähler differentials.
- `WeierstrassModel.lean`: Riemann–Roch construction of coordinates with pole divisors `2P` and `3P`; generation of the function field; nonsingularity over perfect constants; an actual constant-field algebra isomorphism with the Weierstrass function field.
- `Statements.md`: exact source signatures, with their declaration contexts and locators, for every explicit declaration.
- `DivisorZeroAxioms.txt` and `WeierstrassModelAxioms.txt`: compiler-produced type and axiom reports, obtained in separate temporary copies of the final sources.
- `Verification.md`: source hashes, sizes, compilation evidence, restrictions audit, and source provenance.

Namespace: `ZInQ.Contrib.RC53Assist.InvariantDifferential`.

## Principal exact statements

For S2b, the rational specialization has no perfectness or separability hypothesis to supply:

```lean
theorem s2b_rational {L : Type*} [Field L] [Algebra ℚ L]
    (hL : TauCeti.IsFunctionField ℚ L) (hex : IsIntegrallyClosedIn ℚ L)
    (he : TauCeti.IsEllipticFunctionField ℚ L) :
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧
      Nonempty (W.FunctionField ≃ₐ[ℚ] L)
```

`exists_weierstrassModel_of_genus_eq_one` is stronger: it retains the specified rational place and proves that the isomorphism's generic coordinate images have sole poles of orders two and three there. Over arbitrary constants, `exists_weierstrassEquation_of_genus_eq_one` still gives a Weierstrass equation and a function-field isomorphism, but does **not** assert nonzero discriminant. The nonsingularity proof needs perfect constants; this includes `ℚ` and `ℂ`.

For S2c, use the declaration context

```lean
open TauCeti
open WeierstrassCurve.Affine
variable {k : Type*} [Field k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
```

The invariant Weil differential is the image of the Kähler differential under `comparison`, determined by the separating generic first coordinate:

```lean
def invariantWeilDifferential : ↥(weilDifferentialSpace k W.FunctionField) :=
  letI := weilDifferentialSpaceModule W.isFunctionField
  comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
    (transcendental_genericX W) (invariantDifferential W)
```

The divisor computation is:

```lean
theorem invariantWeilDifferential_divisor :
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (invariantWeilDifferential W).2 (invariantWeilDifferential_ne_zero W) = 0
```

The holomorphic line is:

```lean
theorem holomorphicWeilDifferentials_eq_span :
    weilDifferentialFiltration (0 : Divisor k W.FunctionField) =
      Submodule.span k {(invariantWeilDifferential W :
        Module.Dual k ↥(repartitionSpace k W.FunctionField))}
```

The exact Kähler formulation, including uniqueness of the constant, is:

```lean
theorem comparison_mem_holomorphic_iff (η : KaehlerDifferential k W.FunctionField) :
    letI := weilDifferentialSpaceModule W.isFunctionField
    (comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (transcendental_genericX W) η :
          Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField) ↔
        ∃! c : k, c • invariantDifferential W = η
```

These theorems hold in every characteristic. In particular the holomorphic space of the function field of a nonsingular Weierstrass curve over `ℂ` is its `ℂ`-span of the invariant differential.

## Why the comparison is mathematically specified

The comparison does not choose a regular Weil differential as a generator. First it constructs the rational-function differential with divisor `-2[∞]` and local component value `-1` on `X⁻¹` at infinity. Its cotrace along `k(X) → k(W)`, `X ↦ x`, is the Weil-theoretic `dx`. The comparison is the function-field-linear equivalence carrying the universal Kähler `dx` to that cotrace. It carries every `dy` to `(dy/dx) dx`.

The divisor proof then derives

`div(ω) = -div(2y + a₁x + a₃) - 2(x)∞ + Diff(k(W)/k(x))`.

At a place where `x` is regular, the monic equation for `y` bounds the different by the order of `2y + a₁x + a₃`. At a pole of `x`, the monic equation for `y/x²` bounds it by the order of `(2y + a₁x + a₃)/x²`. Thus `div(ω) ≤ 0`. Its degree is `2g - 2 = 0`, and residue-degree positivity forces `div(ω) = 0`.

No residue calculation at an arbitrary point and no hypothesis that `ω` is already regular enters this argument. Independence of the general comparison from the separating parameter is not asserted; the result uses the specified parameter `x` throughout.

## Precise remaining S2a reduction

Let `A/ℚ` be the one-dimensional abelian variety in Shimura's quotient construction, understood as a proper smooth geometrically connected group scheme, and let `e` be its identity.

The general printed statements needed for the differential part can be taken from the manuscript-cited source **Milne, Abelian Varieties, version 2.00 (2008), Chapter IV, Propositions 6.4 and 6.6, printed p. 152, PDF page 158**:

1. On a smooth variety of dimension `d`, the sheaf of differentials is locally free of rank `d`; on a group variety it is free (Proposition 6.4).
2. On a complete geometrically connected variety, evaluation of the global sections of a finite-rank free sheaf at a rational point is an isomorphism (Proposition 6.6).

These are general statements about arbitrary dimension and arbitrary free sheaves, not the conclusion that a one-dimensional abelian variety has genus one. Neither statement is introduced as an axiom or an assumed conclusion in the Lean files.

They give `dimℚ Γ(A, Ω¹_A/ℚ) = 1`. What remains to turn this into a Lean discharge is the following precise geometric dictionary:

1. From `dim A = 1`, properness, smoothness, and geometric connectedness, construct the integral-curve/function-field interpretation of `A`, with its inherited `ℚ`-algebra structure on `A.functionField`. Prove `TauCeti.IsFunctionField ℚ A.functionField` and `IsIntegrallyClosedIn ℚ A.functionField`.
2. Turn the rational identity `e` into a place `P_e : TauCeti.Place ℚ A.functionField` of degree one. This requires the one-dimensional local-ring/valuation-ring dictionary at `e`, not just a point in the carrier of a scheme.
3. Define the relative differential sheaf and prove the natural comparison
   `Γ(A, Ω¹_A/ℚ) ≃ₗ[ℚ] ↥(TauCeti.weilDifferentialFiltration (0 : TauCeti.Divisor ℚ A.functionField))`.
   The new comparison in `DivisorZero.lean` concerns Kähler differentials of a Weierstrass **function field**, not this scheme-level identification for an arbitrary group scheme.
4. Propositions 6.4 and 6.6, together with the comparison in item 3 and the existing theorem that the holomorphic Weil dimension is the genus, then give genus one. The proved `s2b_rational` applies to the resulting function-field package.
5. To identify Shimura's original quotient with the smooth projective Weierstrass curve itself, upgrade the function-field isomorphism to an isomorphism of the smooth proper curve models, preserving the identity.
6. For Shimura's analytic `D_A`, also identify algebraic global differentials after extension to `ℂ` with analytic holomorphic differentials. The new function-field line theorem alone is not a proof of that algebraic–analytic dictionary.

Mathlib already contains proper geometrically integral group-scheme commutativity and geometrically reduced group-scheme smoothness results in `Mathlib/AlgebraicGeometry/Group/Abelian.lean` and `Group/Smooth.lean`. Consequently the original source's blanket statement that there is no abelian-variety support is too broad. Those results do not by themselves discharge the six dictionary obligations above, and this contribution does not claim S2a.

### Source reading

The Milne PDF was read by text extraction, including its cover and printed p. 152. The cover says version 2.0, March 16, 2008; its bibliographic page says v2.00. Source URL: `https://www.jmilne.org/math/CourseNotes/AV.pdf`. SHA-256 of the PDF bytes read:

`f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef` (1,291,594 bytes).

The manuscript has bibitems `milne-av` and `silverman`. Silverman III.1.5 and III.3.1 are mathematical locators supplied by the target and by the public proof sources; no Silverman page-image reading or human source certification is claimed here. S2b and S2c are kernel-checked proofs, not assumptions justified by those citations.

## Checking

From the repository root, with the selected Lean toolchain on `PATH`, check each final proof independently:

```sh
LEAN_NUM_THREADS=6 taskset -c 32-47 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/InvariantDifferential/DivisorZero.lean
LEAN_NUM_THREADS=6 taskset -c 32-47 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/InvariantDifferential/WeierstrassModel.lean
```

The files require only already compiled imports. No repository-wide build, dependency update, executable target, existing-file edit, commit, or checkout was performed. Both final files use a heartbeat bound of 800000. All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The complete S2 conjunction and Theorem 5.3 are **not** claimed proved. Integration into the owning modules and independent review remain with the maintainers.
