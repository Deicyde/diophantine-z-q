# The analytic points in the Shimura Hecke bridge

**Proved (VERIFIED).** For every model in the fixed proposition and
every `τ : UpperHalfPlane`, there is exactly one `x : CPt X` satisfying
`AtTau N jX tX x τ`. The main theorem is
`ShimuraPointDict.existsUnique_atTau` in
[ShimuraPointDict.lean](../../ZInQKernel/Contrib/OneProof/ShimuraPointDict.lean).
Its assumptions are `2 ≤ N`, integrality of `X.left`, `IsCurve X`,
and `IsX1Gen N X jX tX`. The exact assembly inputs are
`ShimuraPointDict.x1TauPoints : HeckePin.X1TauPoints` and
`ShimuraPointDict.atTau_unique` for single valuedness on the model.
`ShimuraPointDict.constOnTauPoints` applies the existing detection
theorem to the existence result.

The point dictionary is closed. The two composite action laws are
the only additional inputs to `ShimuraHeckeRelations`:
`CoprimeActionLaw` is closure of `IsXi` under products at coprime
positive indices, and `GoodPrimeActionLaw` is closure under the
diamond-corrected recurrence at good prime powers. The two orbit
counts identified in the [prior reduction](shimura-hecke-j.md#smallest-remaining-inputs)
are meant to supply those laws. The per-model
`ShimuraPointDict.exists_xi_of_compositeActions` and global
`ShimuraPointDict.shimuraHeckeRelations_of_compositeActions` take
the laws directly. No new leaf or change to the fixed statements
is needed.

## Proof

All new mathematics is on-the-spot glue, provenance (c). The proof works
with the field of the rational model directly, so it also covers a complex
point whose image on the rational scheme is the generic point.

1. The two holomorphic coordinate extensions have the same polynomial
   relations as the algebraic generators. The identity theorem lets one
   test a relation on any punctured neighbourhood in the upper half-plane.
   The exceptional branches lie in the zero sets of (g_2) and (g_3),
   which are eventually absent on every such punctured neighbourhood.
   Localizing the image of the integral polynomial ring sends the full
   function field to punctured germs. Each germ is meromorphic, and the
   limit of a quotient agrees with the limit required by `AtTau`.
2. The rational functions with a finite limit at the parameter form a
   valuation ring in the function field. Taking limits gives its map to
   `ℂ`. The inverse of a function with no finite limit has limit zero.
3. Properness extends the generic-point map to the spectrum of this ring.
   The stalk at its center is a valuation ring with the same fraction
   field, and the local map to the finite-limit ring is an isomorphism.
   Compose the lift with the complex evaluation map. The stalk and section
   evaluation maps agree, which yields every `RegAt` condition in `AtTau`.
4. Conversely, an `AtTau` point gives the correct stalk value for every
   element of the finite-limit ring. If one of its stalk elements were
   outside the ring, the inverse would be a stalk element vanishing at the
   point. This contradicts the product being one. Thus the point gives a
   lift from the same valuation ring, with the same evaluation map.
   Separatedness makes the lifts equal, and evaluation makes the complex
   points equal.

## Known issues

- The prior [print audit](shimura-steps.md#known-issues) records a misprint
  on Shimura p. 526 in the conjugate-newform sentence before clause (iv):
  the eigenvalue multiplies the conjugate form. This is outside the
  quotient clauses used here.
- The total Euler identity does not by itself identify the Tate
  constituent at a fixed coefficient field embedding. That verification
  is outside this contribution.
- No new manuscript or print error was found in the point comparison. The
  manuscript does not give an analytic point dictionary for the fixed
  Lean model.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L768–770 | OK | The manuscript supplies the Fricke proviso through Li. This assessment follows the prior audit; the point argument does not need the proviso. |
| L770–771 | OK | The cited theorem supplies the quotient construction and total Euler identity under its proviso, as recorded in the prior print audit. |
| L770–773, points used for the quotient's Hecke action | gap filled | The manuscript does not describe the fixed Lean model. The proof realizes its exact complex point test and shows it is single valued. |
| L771–773 | unverified | This work does not check the identification of the specified Tate constituent from the total Euler identity. |
| L11053–11057 | OK | The bibliography identifies the cited Shimura paper, Theorem 1, and its DOI. |

## Lean statements

All new declarations are in `ShimuraPointDict`. The source files print
the axioms of every new theorem, including private helpers.

| Theorem | Statement |
| --- | --- |
| `hasValue_coe` | The value of a represented punctured germ is exactly the limit of its representative. |
| `hasValue_unique` | A punctured germ has at most one finite limit. |
| `hasValue_const` | A constant germ has that constant as its limit. |
| `hasValue_add`, `hasValue_mul`, `hasValue_neg` | Germ limits respect addition, multiplication and negation. |
| `isUnit_germ_of_eventually_ne_zero` | An eventually nonzero function defines a unit in the punctured germ ring. |
| `inverse_germ_eq` | A multiplicative inverse of a represented germ is represented by pointwise inversion. |
| `hasValue_inv_of_not_mem` | If the meromorphic germ of (g) has no finite limit, the germ of (g^{-1}) has limit zero. |
| `finiteValue_spec` | Evaluation on the subring of finite germs gives the unique limit. |
| `algEval_apply` | The integral polynomial evaluation homomorphism agrees with `AfTateOr.ev2`. |
| `exists_polynomial_fraction` | A field generated by two elements consists of quotients of integral polynomials in them with nonzero denominator. |
| `eventually_good` | The (g_2,g_3) extensions are both nonzero eventually at each punctured parameter. |
| `map_punctured_coe` | The inclusion of the upper half-plane maps a punctured neighbourhood filter to its ambient complex punctured neighbourhood filter. |
| `tendsto_quotient_iff` | Quotients of the fixed analytic evaluations and of the extended coordinates have the same finite limits. |
| `polynomialGerm_eq_zero_iff` | An integral polynomial has zero germ iff its algebraic evaluation is zero. |
| `polynomial_eventually_ne_zero` | A nonzero algebraic denominator has eventually nonzero analytic evaluation. |
| `evalOnRange_apply` | The factored germ evaluation agrees on polynomials with analytic evaluation. |
| `evalOnRange_units` | The factored evaluation sends nonzero denominators to units. |
| `fractionRing_of_generation` | The model's function field is the fraction field of the integral polynomial image. |
| `fieldGerm_fraction` | The field-to-germ map takes a polynomial quotient to the quotient of the corresponding evaluations. |
| `fieldGerm_meromorphic` | Every image germ has a meromorphic representative. |
| `hasValue_fraction_iff` | The value of the image of a polynomial quotient is exactly the limit tested by `AtTau`. |
| `regAt_iff_stalk` | `RegAt` is equivalent to having a stalk element with the given function-field image and complex value. |
| `spec_to_rat_eq` | Two maps from the same affine spectrum to `Spec ℚ` coincide. |
| `specMap_to_generic` | The map from the generic point factors through the spectrum of any stalk by the fraction-field inclusion. |
| `centerMap_comp` | The stalk map at the valuative center induces the original inclusion into the function field. |
| `centerMap_surjective` | The stalk at the valuative center maps onto the valuation subring. |
| `exists_regAt_of_valuation` | For a valuation subring over ℚ with a map to ℂ, there is a complex point giving the prescribed `RegAt` values for all its elements. |
| `point_eq_of_stalk_to_valuation` | Two complex points whose compatible stalk maps factor through the same valuation and complex evaluation coincide. |
| `exists_atTau` | For each fixed model and parameter, some complex point satisfies `AtTau`. |
| `stalk_witness_of_hasValue` | An `AtTau` point gives the prescribed stalk evaluation for any rational function with a finite limit. |
| `stalk_mem_tauValuation` | Every element of a stalk at an `AtTau` point is in the finite-limit valuation ring. |
| `tauValue_stalkToTau` | The map from that stalk to the valuation ring intertwines complex evaluation and the limit homomorphism. |
| `atTau_unique` | For each fixed model, `∀ τ x y, AtTau N jX tX x τ → AtTau N jX tX y τ → x = y`. |
| `existsUnique_atTau` | For every such model and `τ`, `∃! x : CPt X, AtTau N jX tX x τ`. |
| `x1TauPoints` | `HeckePin.X1TauPoints`. |
| `constOnTauPoints` | `HeckePin.ConstOnTauPoints`. |
| `exists_xi_of_compositeActions` | Under the fixed per-model hypotheses, the supplied prime formulas and the coprime and good-prime-power composite action laws produce the family of operators and its Hecke relations. |
| `shimuraHeckeRelations_of_compositeActions` | Those two action laws for the models in the fixed proposition imply `ShimuraSteps.ShimuraHeckeRelations`. |

## Verification

VERIFIED with Lean 4.35.0. All four `ShimuraPointDict*.lean` modules
compiled with `lake env lean`, one at a time.
[Integration.lean](../../scratch/shimura-point-dict/Integration.lean)
also compiled and checks both global inputs and the exact per-model
statement and composite assembly types. The
[axiom output](../../scratch/shimura-point-dict/Axioms-output.txt)
covers 40 theorems and reports only `propext`, `Classical.choice`,
and `Quot.sound`.
