# Integral central calibration model

## Result

A retained finite-free integral replacement, its Smith core-and-disks normalization, and preservation of its quasi-isomorphism under coefficient extension are constructed. The constructor `integralBlockCentralModel` returns the existing `IntegralBlockCentralModel` after the arithmetic cohomology shape and the quasi-isomorphism of the canonical compact-to-finite reduction are supplied. No disk-order equality is assumed.

Source SHA-256: `4b0edd6b33596f7f0145efcce5df12b5605edcd911c7c3fb7c6b0128b17e0888`.

## Construction

1. **Finite free replacement.** For each integral cohomology module, choose a surjection from a finite free module. Its kernel is finite free over the principal ideal domain. Lift the generators to cycles by projectivity, and lift their relations to actual bounding cochains. In degree n the model has the generators of Hⁿ and the relations of Hⁿ⁺¹. The resulting cochain comparison is proved to induce an isomorphism in every degree. This construction does not require the original cochain modules to be finite free or bounded.

2. **Flatness of the genuine compact complex.** The Tate module is finite free of rank two. Continuous cochains with torsion-free coefficients, their submodules defining the Kummer conditions, and the products forming the Selmer cone are torsion-free. Over the two-adic principal ideal domain these modules are flat. No finite-support hypothesis is needed for this flatness statement.

3. **Integral Smith normalization.** Smith bases for the relation submodules separate the free core coordinates from elementary disks with nonzero coefficients. The separated model is an actual integral chain isomorphism of the finite-free replacement. The theorem `DiagonalResolution.coreRank_eq_finrank` identifies its core rank with the original integral cohomology rank. All disk matrices are constructed diagonal matrices, with nonzero determinants, including the empty determinant.

4. **Coefficient extension.** An additive coefficient-extension functor preserves an actual homotopy equivalence without flatness of the new ring. More strongly, a quasi-isomorphism between complexes of flat modules over a principal ideal domain remains a quasi-isomorphism after extension to any commutative coefficient ring. The proof uses exactness after tensoring two consecutive exact pairs, flatness of the mapping cone, and its acyclicity. It applies to both the integer residue rings and the finite calibration coefficient rings.

5. **Central block model.** Under the cohomology shape below, the general elementary model is integrally isomorphic to the required four-degree block complex. The retained coordinates, the integral normalization, the comparison to the compact central Kummer complex, and the nonzero disk determinants are constructed. The finite-fibre comparison is exactly the extended integral comparison followed by the canonical Kummer reduction.

6. **Determinant basis.** The retained basis is the displayed integral block basis transported along the constructed normalization. Every resulting basis-change determinant is a two-adic unit, and the alternating inverse determinant-line factor has central valuation zero. This is a statement about the constructed integral basis; it does not identify an unrelated rational class/functional coordinate with that basis.

## Exact remaining inputs

Write

```lean
C := compactKummerComplex G.S (centralCurve G) (centralFullTorsion G)
```

The permitted finite-generation input is retained with exactly the requested type:

```lean
hfinite : ∀ n, Module.Finite ℤ_[2] (C.homology n)
```

The arithmetic shape is `CalibrationCohomologyShape (compactCentralComplex G)`, whose fields are:

```lean
outside : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton (C.homology n)
rank_one : Module.finrank ℤ_[2] (C.homology 1) = 1
rank_two : Module.finrank ℤ_[2] (C.homology 2) = 1
rank_three : Module.finrank ℤ_[2] (C.homology 3) = 0
```

Finite generation alone does not imply this amplitude or these ranks. The original continuous cochain complex is not termwise bounded. These statements require the arithmetic Selmer cohomology calculation for the calibration leaf, including the needed finiteness of the relevant arithmetic groups.

The remaining derived-reduction input is precisely:

```lean
hreduce : ∀ i : ℕ, i ≠ 0 → QuasiIso (canonicalCentralReductionMap G i)
```

The theorem `retainedCentral_fibre_quasiIso_iff` proves that the finite-fibre requirement on the constructed retained model is equivalent to this condition on the fixed canonical map. Thus there is no additional model-dependent finite-fibre assumption. Construction of the canonical coefficient map and compatibility on individual Kummer cocycles do not by themselves prove its quasi-isomorphism.

Matching the three constructed determinant scalars with prescribed rational calibration disks, and identifying their lengths with rational torsion and Tate–Shafarevich orders, remain separate arithmetic comparisons. Neither `DiskArith` nor those length equalities are used here.

## Scope of the normal form

The matrix-disk model retains noncyclic torsion. A single scalar disk cannot generally replace a noncyclic torsion module by an integral quasi-isomorphism. Consequently the matrix version is constructed; cyclicity is not silently imposed to produce `CanonicalIntegralCentralModel`.

The existing finite-free model lemmas for Artin local rings require a nilpotent maximal ideal. The maximal ideal of ℤ₂ is (2), which is not nilpotent, so those lemmas cannot be applied directly. The new principal-ideal-domain construction avoids that hypothesis. Its comparison is a quasi-isomorphism, not an asserted homotopy equivalence of arbitrary flat compact cochains.

## Verification

The mathematical source and the scratch certificate both compile by single-file Lean checking. The certificate records the exact signatures and kernel-reported axioms for all 58 theorems and 11 main proof-bearing constructors. Every printed axiom list is a subset of `propext`, `Classical.choice`, and `Quot.sound`; no nonstandard axiom occurs. The source contains no proof placeholders, new axioms, evaluation commands, or new notation or syntax declarations.
