# Central universal coefficients over the specified quadratic field


## Shipped edition (2026-11-18)

The shipped modules are `GenuineObjects`, `IntegralAlgebra`, `CoefficientComplex`, `DiscreteSelmer`, `Arithmetic` and `CentralComparison`, importing the integrated `CentralSelmer.QuadraticDescent` and `CentralSelmer.QuadraticDescentPlug` directly. The copies of those two modules and the single-file concatenation `Universal.lean` used while the integrated modules were not built are not shipped.

## Result and status

The genuine universal-coefficient map, its integral-basis coordinate map `j`, the proof `BoundedDefects j`, and the rational identification `eK` are constructed and compiled **conditional on the two named arithmetic inputs below**. Witnesses of those inputs are not constructed in this contribution.

The coordinate map is injective. Its actual cokernel is isomorphic to the torsion of the genuine compact Kummer complex in degree two. One fixed nonzero power of two kills both defects. No finiteness of the whole Shafarevich–Tate group is assumed.

`Universal.lean` is the standalone development. The other Lean files provide the alternative modular layout. The full exact statements and kernel axiom output for all 200 theorems, and all 309 named declarations, are in `StatementsAndAxioms.txt`. Of the theorems, 64 are new and 136 are the copied quadratic-descent results. `AxiomSummary.tsv` is the per-declaration summary; `DeclarationIndex.tsv` locates each declaration in the modular sources. `FileManifest.tsv` gives the source files and audit receipts with their sizes and SHA-256.

## Fixed genuine objects

- `QuadraticField k = IntermediateField.adjoin ℚ {sqrtK k}`. Its fixing subgroup is proved to be the group `galK (sqrtK k)` used in the genuine `SelK ℓ k`.
- `arithmeticCompactComplex ℓ k S hFull` is precisely `compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull`.
- `arithmeticRationalComplex ℓ k S hFull` is precisely the corresponding `rationalKummerComplex`, the scalar extension to the field of two-adic numbers.
- The target is literally `SelK ℓ k`, defined by the image of global two-primary coefficient cohomology being locally trivial at every finite and infinite place. No auxiliary target group is chosen.
- `S` denotes the fixed place support of this compact complex, not an auxiliary additive group. Full two-power torsion over the corresponding unramified extension and ellipticity are the structural parameters of the genuine complex.

Write `C = arithmeticCompactComplex ℓ k S hFull`, `M = C.homology 1`, and `D = Q2Z2`. The coordinate rank is

```lean
arithmeticRank ℓ k S hFull =
  Module.finrank ℤ_[2] (M ⧸ Submodule.torsion ℤ_[2] M)
```

`arithmeticFreeBasis` is a basis of this actual integral quotient by torsion. It is obtained by finite generation and the principal ideal domain structure, not supplied as a free comparison input. Both the divisible coordinates and `arithmeticRationalH1Equiv` use this same basis. No integral splitting of `M` is chosen.

## Exact named arithmetic input types

The following is the common context, with the existing mathematical namespaces open:

```lean
variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))
```

### Finite generation of compact Kummer cohomology

```lean
structure KummerCohomologyFinite : Prop where
  finite_one : Module.Finite ℤ_[2]
    ((arithmeticCompactComplex ℓ k S hFull).homology 1)
  finite_two : Module.Finite ℤ_[2]
    ((arithmeticCompactComplex ℓ k S hFull).homology 2)
```

This is the consequence of perfection needed here, as used in manuscript lines 5261–5263. It says nothing about finiteness of the full discrete Selmer or Shafarevich–Tate group.

### Coefficient and local-Kummer comparison of complexes

```lean
structure KummerCoefficientComparison where
  finite_support : S.Finite
  comparison :
    (integerCoefficientComplex
      (arithmeticCoefficientComplex ℓ k S hFull)).truncLE 1 ⟶
        discreteSelmerComplex ℓ k
  quasiIso : QuasiIso comparison
```

Here `arithmeticCoefficientComplex` is the cokernel complex of the canonical map from the genuine compact complex to its rationalization, with rational coefficients restricted to integral scalars. `integerCoefficientComplex` only restricts those scalars further to the integers. `discreteSelmerComplex` is the actual continuous Selmer cocycle complex of `SelK ℓ k`, with all global zero-cochains retained.

The comparison is the standard arithmetic realization of the coefficient sequence and the local Kummer conditions underlying manuscript lines 4007–4018 and 5305–5311. Its proof must identify the two Galois-cochain realizations and the genuine local conditions, including degree zero. This contribution constructs neither that cochain map nor its quasi-isomorphism proof. The intended standard comparison is for the imaginary quadratic branch of the manuscript; no existence is claimed for arbitrary supports or real quadratic fields.

This input contains no `j`, no rational basis, no coordinate rank, no bounded-defect condition, no corank assertion, and no matrix-model data. It is not an assumption of the requested divisible-group comparison. In particular the rank-one hypothesis is not used in the construction or bounded-defects proof.

## Proved universal-coefficient sequence

Every term of the genuine compact complex is proved torsion-free. The canonical coefficient sequence is therefore a short exact sequence of complexes. Flat base change identifies rational cohomology with the actual tensor product. If `Q(C)` is the canonical cokernel complex of `C → C ⊗ ℚ₂`, the cohomology long exact sequence constructs and proves

\[
0\longrightarrow H^1(C)\otimes_{\mathbb Z_2}D
 \longrightarrow H^1(Q(C))
 \longrightarrow H^2(C)_{\mathrm{tors}}\longrightarrow0,
\]

with the middle term given by the coefficient quotient model. Transport through the named cochain comparison gives the corresponding sequence with middle term `SelK ℓ k`.

`arithmeticUniversalCoefficientMap` is that map, with the tensor factors in the manuscript's order. On a pure tensor represented by a two-adic scalar `q`, its value is the cohomology coefficient projection of `q ⊗ x`, transported through the cochain comparison. This formula is proved in `arithmeticUniversalCoefficientMap_formula`.

For witnesses `I : KummerCoefficientComparison ℓ k S hFull` and `F : KummerCohomologyFinite ℓ k S hFull`, the principal conclusions are:

```lean
Function.Injective (arithmetic_j ℓ k S hFull I F)
```

```lean
BoundedDefects (arithmetic_j ℓ k S hFull I F)
```

```lean
∃ n : ℕ, (2 ^ n : ℕ) ≠ 0 ∧
  (∀ x, arithmetic_j ℓ k S hFull I F x = 0 →
    (2 ^ n : ℕ) • x = 0) ∧
  (∀ y : SelK ℓ k, ∃ x,
    arithmetic_j ℓ k S hFull I F x = (2 ^ n : ℕ) • y)
```

The exact cokernel identification is the defined additive equivalence

```lean
(SelK ℓ k ⧸ (arithmetic_j ℓ k S hFull I F).range) ≃+
  Submodule.torsion ℤ_[2]
    ((arithmeticCompactComplex ℓ k S hFull).homology 2)
```

The fixed power is derived from an annihilator of the whole degree-two torsion module. It is not a point-dependent annihilator and is not an input bound.

`arithmetic_j_on_tensor` and `arithmeticRationalH1Equiv_on_tensor` prove explicitly that `j` and `eK` use the same actual integral free-part basis. `arithmeticRank_eq_rational_finrank` identifies their number of coordinates with the rational Kummer cohomology dimension. Only afterwards does `arithmeticRank_eq_one` use the full Selmer corank-one hypothesis, including any divisible Shafarevich–Tate part, to deduce that this genuine rank is one.

## Plug into the existing central comparison

`centralSelmerComparisonOfCompactKummer` is compiled with exactly the following call:

```lean
centralSelmerComparisonOfQuadraticDescent
  hk Dm CU e1 e2 hzero hd
  (arithmeticRationalComplex ℓ k S hFull) i
  (arithmeticRationalH1Equiv ℓ k S hFull F)
  (arithmetic_j ℓ k S hFull I F)
  (arithmetic_j_boundedDefects ℓ k S hFull I F)
```

Thus `r`, `eK`, `j`, and `hj` are not free parameters of the new wrapper. The model-side comparison still has the exact type

```lean
i : arithmeticRationalComplex ℓ k S hFull ⟶
  scalarChangedComplex Rings.rhoT CU
```

with `[QuasiIsoAt i 1]`. Given it, `hcentral_of_compactKummer` and `central_dimensions_of_compactKummer` prove the existing base-zero matrix rank and the two central dimensions. This contribution does not construct that retained primitive-to-model comparison and does not infer it from an unconstrained matrix.

## Verification and source compatibility

All modular Lean sources compile. The standalone source also compiles with the prescribed single-file command, six threads, CPU affinity 160–175, and niceness 10. The maximum heartbeat setting is 600000. The complete dependency union for the 309 audited named declarations is exactly:

```text
propext
Classical.choice
Quot.sound
```

The per-theorem outputs, rather than only this union, are retained in `StatementsAndAxioms.txt` and `AxiomSummary.tsv`.

The quadratic-descent source was copied byte-for-byte. The quadratic-descent plug differs from its source only in the relocated import of that copied module. No existing source file was edited. No Git command, `lake build`, `lake update`, or `lake exe` was run. Scratch inspection sources were removed after the audit.

The standalone and modular layouts are alternatives: do not import both. The compatibility copies declare the original quadratic-descent namespaces; likewise do not load them together with their original counterparts.

## Precisely still open

1. Supply the two finite-generation proofs in `KummerCohomologyFinite` for the genuine compact complex.
2. Construct the actual coefficient/local-Kummer cochain comparison in `KummerCoefficientComparison` and prove its quasi-isomorphism, retaining degree zero and agreeing with the full Selmer conditions at every place.
3. For the final central matrix conclusion, supply the separate retained map `i` with its degree-one quasi-isomorphism to the specialized genuine model.

No existential divisible-group map or hypothesis equivalent to `BoundedDefects j` is left as an input. The result is a compiled conditional construction, not an unconditional proof of the remaining arithmetic comparison or of Theorem 5.3.
