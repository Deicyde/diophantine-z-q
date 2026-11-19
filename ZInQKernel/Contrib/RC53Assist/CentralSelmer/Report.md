# Central Selmer comparison: verified partial proof


## Correction after independent review (2026-11-18)

An independent review found that the remaining inputs of
`centralSelmerComparisonOfSpecializedModel`, as typed, are not tied to arithmetic objects: input 1 is
met by taking `K` to be the scalar-changed model itself with `i` the identity, and input 3 by taking
`S := fullSelmerProduct` with `f` the identity; nothing in the signature mentions the quadratic field.
`Restatement.lean` records `inputs_iff_hcentral`: under `SelmerCorankOneOverK`, the remaining bundle is
equivalent to `hcentral`. So this contribution proves the algebraic steps and supplies a constructor,
but it does not shrink the base-zero leaf: `central` and `hcentral` stay open at their present strength
until the inputs are supplied by the genuine objects (the rational Kummer complex of the actual local
conditions, the Selmer group over the quadratic field, and the restriction-corestriction pair). Further
notes from the review: `universalCoefficientsRatTateEquiv` takes an arbitrary basis that is not tied to
`j`; `hzero : CU.d 0 1 = 0` is not a field of `BaseZeroCoreLimit` or `BaseZeroCore`, so wiring needs an
interface change; `Comparison.lean` uses `set_option backward.isDefEq.respectTransparency false` at one
declaration (needed for elaboration; it does not affect soundness). Earlier text below that describes
the inputs as "the genuine full Selmer group over the quadratic field" describes the intended
instantiation, not what the types enforce.

## Result and scope

The product, rationalization, eigenspace, matrix-cohomology, and coefficient-specialization steps are proved. The conditional constructors return the exact existing `CentralSelmerComparison` type, and `hcentral_of_specializedModel` returns the exact base-zero rank field. The actual arithmetic instance is **not** constructed, so the original comparison gap is **not closed**.

The contribution contains one self-contained Lean source importing only the existing central-comparison module. The supplied starting revision was `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc`. No version-control operations or pre-existing source edits were performed.

## Exact target in mathematics

Put `A = LambdaT = Z₂[[t]]_(t)` and let `rhoT : A → Q₂` be the residue map. For a square `(m+1)`-by-`(m+1)` matrix `Dm`, the target consists of a Q₂-linear equivalence

`ker ((Dm.map rhoT).mulVecLin) ≃ₗ[Q₂] RatTate S₁ × RatTate S₂`.

In the intended instance,

- `S₁ = selmerTwoPower (Ecurve ℓ)`;
- `S₂ = selmerTwoPower (Etw ℓ k)`;
- `RatTate S = Hom_cont(Q₂, S)` for the discrete topology on `S`, implemented as additive maps killing `2^N Z₂` for some `N`;
- `(c • v)(x) = v(c x)` is the scalar action.

This rationalizes the full discrete Selmer group through its rational Tate module. It is not the tensor product of Q₂ with that discrete torsion group. In particular the divisible Shafarevich–Tate contribution is retained.

## Manuscript argument and cited sources

The base-zero proof, lines 4341–4352, supplies the statement that full Selmer corank one gives central dimensions `(1,1)`. The underlying identifications are:

1. Lines 3952–3962: the ordinary rational Kummer complex `K₀` compares by a quasi-isomorphism with the central primitive complex. Unit-disk cancellation must retain an actual homotopy equivalence before specialization.
2. Lines 4007–4018 and 5305–5311: universal coefficients give `0 → H¹(C_K) ⊗ Q₂/Z₂ → Sel₂∞(E/K) → H²(C_K)_tors → 0`. The last term is finite. Rationalization therefore gives the full Selmer rational Tate module, not just the Mordell–Weil subgroup.
3. Lines 2616–2626: quadratic restriction/corestriction and sum-and-difference maps have bounded two-primary defects. After inverting two, the two eigenspaces give the Selmer groups over Q of `E` and `E^(k)`. There is no integral direct-sum assertion.
4. The existing central-comparison results use the two rational coranks `1` and `0` and rank–nullity to obtain `(Dm.map rhoT).rank = m` and one-dimensional kernel and cokernel.

The bibliography was checked: Milne, *Arithmetic Duality Theorems*; Nekovar, *Selmer Complexes*; and Silverman, *The Arithmetic of Elliptic Curves*, are cited sources. No new printed leaf, from these or any other source, was assumed.

## Proved components

All names below are in `ZInQ.Manuscript.RC53Assist.CentralSelmer`.

- `ratTate_map_bijective_of_boundedDefects`: an additive map with bounded kernel and cokernel induces a bijection on rational Tate modules. A scaled inverse is constructed in the proof; the result is not obtained by matching dimensions.
- `boundedDefects_of_scaledInverse`: maps whose two composites are multiplication by a nonzero integer have bounded defects.
- `boundedDefects_of_finite`: a finite kernel and finite cokernel give bounded defects.
- `ratTateEigenspaceEquiv`: an additive involution gives `RatTate S ≃ₗ[Q₂] RatTate S⁺ × RatTate S⁻` by the sum-and-difference map. Both integral defects are killed by two.
- `h1ProdAddEquiv` and `h1ProdAddEquiv_naturality`: continuous H¹ commutes with coefficient products, compatibly with every compatible-pair pullback and hence with localization.
- `mem_fullSelmerProduct`, `fullSelmerProductAddEquiv`, and `fullSelmerProductRatTateEquiv`: the product of the genuine two-primary coefficient modules, with genuine point-cohomology local triviality conditions at all places, gives precisely the product of the two existing full Selmer groups and then their rational Tate modules. No finiteness of Shafarevich–Tate is used.
- `modelHomologyOneEquiv`: the first cohomology of a matrix model with zero incoming differential is its matrix kernel.
- `matrixKerEquivOfQuasiIso`: a degree-one quasi-isomorphism transports that identification to the ordinary rational Kummer complex.
- `specializedModelHomologyOneEquiv`: coefficient extension of the actual complex along a ring map replaces the matrix by its entrywise image and identifies specialized H¹ with the resulting kernel. No flat cohomology-base-change assertion is assumed.
- `universalCoefficientsRatTateEquiv`: a rational cohomology basis and an actual bounded-defect map from the corresponding power of Q₂/Z₂ to full Selmer give the rational Tate comparison.
- `centralSelmerComparisonOfKummerModel`, `centralSelmerComparisonOfUniversalCoefficients`, and `centralSelmerComparisonOfSpecializedModel`: conditional constructors returning the exact existing comparison type.
- `central_dimensions_of_KummerModel`: under `SelmerCorankOneOverK ℓ k`, these inputs give the rank field and one-dimensional central kernel and cokernel.
- `hcentral_of_specializedModel`: the same for the original integral `CU`, `Dm`, `e1`, `e2`, and `hd` fields, with coefficient specialization performed in the proof.
- `no_comparison_identity`: coranks `1` and `0` do not imply a comparison for an unconstrained identity matrix. This rules out an unconditional deduction from the coranks alone.

The accompanying compiler output records the exact Lean types of every public theorem and construction, plus the four private helper theorems, and all of their requested axiom reports. The source records the full statements, including the continuity and compatibility hypotheses hidden by proof elision in pretty-printed output.

## Exact remaining inputs

For `centralSelmerComparisonOfSpecializedModel`, the unresolved arithmetic work is to supply the following **for the intended base model**, rather than for freely chosen substitute objects:

1. **Actual model and Kummer comparison.** Construct the ordinary rational Kummer complex `K₀` and its retained map

   `i : K₀ ⟶ scalarChangedComplex rhoT CU`, with `[QuasiIsoAt i 1]`.

   This must include the arithmetic local-condition comparison and the identification of the selected finite model with the primitive complex. The displayed `CU` fields alone do not record that identification. The constructor also requires `CU.d 0 1 = 0`; this follows from genuine two-term support, but it is not a field of the displayed base-model structures.

2. **Actual full Selmer group and universal coefficients.** Construct `S = Sel₂∞(E/Q(sqrt k))`, a cohomology coordinate equivalence

   `eK : K₀.homology 1 ≃ₗ[Q₂] (Fin r → Q₂)`,

   and the map from the actual integral cohomology lattice quotient

   `j : (Fin r → Q2Z2) →+ S`, with `BoundedDefects j`.

   The coordinates must be matched with that lattice quotient. The map's injectivity and finite cokernel in the manuscript suffice, by the proved bounded-defect rationalization.

3. **Actual quadratic Selmer descent.** Construct

   `f : S →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)`, with `BoundedDefects f`,

   by the genuine restriction/corestriction and twist identifications, preserving all local conditions. The algebraic involution splitting and bounded-defect rationalization are proved; the arithmetic identification of its eigenspaces with these two rational Selmer groups is not supplied.

`BoundedDefects` means that nonzero integers `a,b` annihilate the kernel and cokernel: `f x = 0 → a • x = 0`, and every `b • y` is in the image. Fixed powers of two suffice; finite defects also suffice.

Once these data exist, the conditional constructor can be used verbatim as the `central` field. Its `.hcentral hSel.1 hSel.2`, or the named `hcentral_of_specializedModel`, supplies the existing `hcentral` field. No change to the protected interfaces is required.

## Verification

- Single-file elaboration completed with exit status zero using the specified CPU affinity, six Lean threads, and priority.
- The prerequisite build log showed completion before the first Lean invocation.
- The final compiler output contains no errors or warnings.
- Twenty public proof-bearing declarations and four private helper theorems were audited.
- All axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; `boundedDefects_of_scaledInverse` uses only `propext`.
- No proof placeholders, added axioms, evaluation commands, custom notation or syntax, or heartbeat increases were introduced.
- No other source files were edited, no commits or builds were made, and no other agents or people were contacted.

An axiom audit checks the foundations of a conditional proof. It does not discharge the arithmetic hypotheses listed above.
