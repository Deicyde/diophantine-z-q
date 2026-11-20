# The group law of the fixed projective Weierstrass model

**Proved the scheme group law on the fixed target.** For every elliptic Weierstrass equation `E` over `ℚ`, `projectiveGroup_exists` proves the exact remaining statement of the previous report:

```lean
∃ g : GrpObj (projectiveTarget E), letI := g
  ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E,
    projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left
```

The unit is the existing rational point at infinity. The multiplication and inverse are scheme morphisms over `ℚ`, and their evaluation agrees with Mathlib's point law over every field over `ℚ`. For the geometric cusp comparison, the existing `projectiveAbVar` and `targetPeriodEquiv` apply to this same model.

`hElkikMD_atScale` supplies the group instance and its point law to `hElkikMD_atScale_of_projectiveGroup`. That theorem factors the based morphism through the represented Jacobian and computes the scaled cusp symbol for every finite rational cusp label. This supplies the weighted comparison `hAJ` in the existing Elkik reduction. The scale witness remains an explicit input.

The construction of the group law uses only the coefficients of the fixed Weierstrass equation. The cusp assignments, the represented Jacobian, and the period homeomorphism from the preceding runs are unchanged. The complex point comparison with `ℂ/Lat` uses the existing additive period equivalence and therefore has the same periods and normalization as the previous run.

Mathlib's secant triple gives the usual sum where its coordinates do not all vanish. On the diagonal it vanishes identically. A second polynomial triple in short Weierstrass coordinates agrees with Mathlib's doubling triple there. The comparison off the diagonal uses two polynomial identities modulo the two curve equations, with separate cases for opposite points and infinity. A rational linear change of coordinates with leading coefficient one computes the second triple in the original fixed equation. The two formulas thus cover all pairs on field points, and each represents addition wherever nonzero. These are on-the-spot arguments (c), using Mathlib's formulas and its existing point group law.

For the scheme construction, on an affine neighborhood first normalize each input vector by a unit coordinate. The coordinate ratios are in the degree zero localization of the corresponding basic open. At any point of the affine neighborhood, one candidate output has a coordinate nonzero in its residue field. Localize at that coordinate to make it a unit, and use the corresponding chart of the target. Reducedness ensures the output equation holds over the chart ring: it holds over the fraction fields of all prime quotients, so the error lies in the nilradical. The formula pulls back to the usual point law; on the chart overlaps separatedness and reducedness give equality of the maps by checking residue fields. The same construction applies to Weierstrass negation. The rational section at infinity supplies the unit. Products of the model are reduced over the perfect field `ℚ`, so the group diagrams likewise follow by checking the Mathlib point laws. This construction is on the spot (c).

## Statements and consumers

The following declarations build the group input for
`hElkikMD_atScale_of_projectiveGroup`. None supplies a rational scale witness.

| Declaration | Statement and role |
| --- | --- |
| `symmetricAddition_map`, `symmetricAddition_smul`, `symmetricAddition_comm`, `symmetricAddition_atInfinity` | Ring maps commute with the second triple; scaling the inputs by `u,v` scales it by `(uv)^2`; interchanging the inputs preserves it; at `[0:y:0]` in the first input its value is `(y² * Q 1) • Q`. |
| `short_eqn_affine`, `symmetricAddition_secant`, `symmetricAddition_opposite` | On the short affine chart the equation is `y² = x³ + ax + b`; the first two components of the second triple agree with the secant after cross multiplication; the first and third vanish at opposite affine points. |
| `symmetricAddition_dbl_affine`, `symmetricAddition_diagonal`, `symmetricAddition_affine`, `symmetricAddition_eq_smul_add` | On the diagonal the second triple equals `dblXYZ`, first in the affine chart and then globally. On a pair of nonsingular vectors the second triple is a possibly zero scalar multiple of Mathlib's sum, first for affine points and then for every pair. |
| `vector_atInfinity`, `projectiveNonsingular_ne_zero`, `projectiveAddition_cover` | A solution with zero last coordinate has the form `[0:y:0]`; a nonsingular vector is nonzero; between `addXYZ` and the second triple at least one is nonzero at every short Weierstrass pair. |
| `additionShortChange_short`, `linearCoordinates_map`, `linearCoordinates_smul`, `linearCoordinates_equiv`, `linearCoordinates_ne_zero` | The displayed rational change sets `a₁,a₂,a₃` to zero. Its projective coordinate map commutes with ring maps and rescaling, respects projective equivalence, and takes nonzero vectors to nonzero vectors. |
| `linearCoordinates_equation`, `nonsingular_of_equation_ne_zero`, `linearCoordinates_toAffine` | The linear map transports the curve equations. In an elliptic equation any nonzero solution vector over a field is nonsingular. The coordinate map agrees with the existing affine additive equivalence, including at infinity. |
| `additionCoordinates_fields`, `additionCoordinates_map` | On the fixed equation over any field over ℚ at least one triple is nonzero, and each nonzero triple solves the equation and evaluates to the group sum. The triples commute with maps of ℚ coefficient rings. |
| `denominatorUnit_val`, `chartFraction_val`, `chartRatio_val`, `projectiveChartRatio_self` | In the ordinary localization, the chosen unit is the image of the chart coordinate; a chart fraction is its numerator times the requisite inverse power, a coordinate ratio has denominator of degree one, and the chart ratio of the normalizing coordinate is one. |
| `projectiveChart_dehomogenize`, `projectiveChart_equation`, `projectiveChart_ringHom_ext` | Evaluating a homogeneous degree `n` polynomial in the ratios is dividing its class by the normalizing coordinate to power `n`. The vector of ratios satisfies the curve equation. Maps from the chart ring are determined by the three ratios. |
| `projectiveEvalAway_fraction`, `projectiveEvalAway_overlap`, `projectiveChartEval_ratio` | Evaluating a localized fraction with unit denominator is evaluation of the numerator divided by the denominator power; the evaluation commutes with restriction to overlaps; after multiplying a chart evaluation of a ratio by the denominator coordinate one recovers its numerator coordinate. |
| `projectiveChartMorphism_map`, `projectiveChartMorphism_independent` | The map from an affine source defined by a solution vector and a unit coordinate commutes with coefficient maps, and is independent of which unit coordinate is used. |
| `zChartInclusion_point_ne_origin`, `chartCoord_mem_iff`, `projectiveValue_chartMorphism`, `projectiveValue_fromChart` | The third chart omits infinity; coordinate vanishing at a chart point is equivalent to vanishing of the corresponding ratio. The two descriptions of a field point (solution vector and chart ring map) evaluate by Mathlib's `Projective.Point.toAffine`, including at infinity. |
| `projectiveUnit_value`, `projectiveHom_ext`, `projectiveHom_ext_value` | The rational infinity section has value zero over every field over ℚ. Equality of maps from a reduced source to the target over ℚ can be checked on field points; bijectivity of `projectiveValue` lets one check equality there by the evaluated points. |
| `projectiveTarget_reduced`, `projectiveTarget_product_reduced`, `projectiveTarget_unit_product_reduced`, `projectiveTarget_product_unit_reduced`, `projectiveTarget_square_reduced` | The original model, its product with any reduced locally Noetherian ℚ-scheme, the products with the tensor unit on either side, and its own square are reduced. |
| `projectiveGroupOfOperations` | From individual multiplication and inversion morphisms inducing the point laws over all fields over ℚ, constructs `GrpObj (projectiveTarget E)` with the specified infinity section. |
| `schemeMapsToRat_unique`, `overlapEq`, `fieldPoint_lifts` | Two maps from any scheme to `Spec ℚ` agree. Two maps to the fixed Proj from a reduced overlap agree if their evaluated field points agree. A field point in the image of an open immersion lifts through it. |
| `projectiveMorphism_of_local`, `equation_of_field_evaluations` | Local affine maps giving the same point rule glue to a global morphism with that rule. A vector over a reduced ℚ-algebra satisfies the equation if it does so under every map to a field over ℚ. |
| `openLift_ring_map`, `projectiveChart_covers`, `projectiveMorphism_of_formulas` | A map from an affine scheme whose image lies in a chart factors through its chart ring. The three charts cover. A family of natural ring formulas with everywhere nonzero coverage and the specified field point rule gives a global morphism with that rule. |
| `exists_projectiveMultiplication`, `exists_projectiveInversion` | There is a morphism from the square to the fixed target inducing Weierstrass addition over every field over ℚ, and a morphism from the target to itself inducing Weierstrass negation over every such field. |
| `projectiveGroup_exists` | The displayed existence theorem; supplies both the `GrpObj` instance and `hAdd` in `hElkikMD_atScale_of_projectiveGroup`. |
| `hElkikMD_atScale` | For the existing newform, periods, genus partner, geometric cusp torsion print, and explicit rational scale witness, gives `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar E Lat d`. It supplies the compatible group realization for the inherited at-scale comparison, hence the actual `hAJ` used by `hElkikMD_of_elkikTorsion`. |

The local morphism and polynomial formula inputs are construction data for tex 1785–1787. Local morphisms realizing a single operation near each point do not assume an overlap agreement, global representability, or group laws. The polynomial formula inputs consist of natural ring formulas and identities over fields; they do not assume scheme morphisms inducing the operation. The group diagram criterion takes two individual morphisms and their evaluation laws, leaving the identity, inverse, and associativity diagrams to prove. No new printed leaf is added.

## Exact remaining inputs

Here `E = Ecurve ℓ` and `N = newformLevel E`. The scale input is explicit: neither the at-scale morphism nor the cusp comparison is used to infer it.

| Input | Tex | Owner and size |
| --- | --- | --- |
| `hr : ∃ c : ℚ, (c : ℂ) = κ`, with the same `κ` as `hκ : IsParamScale N f.toCuspForm Lat κ`. | 1785–1787, 1825–1828 | Sibling scale rationality lane. |
| `ElkikPrint.ManinDrinfeldTorsion N (algebraicCuspClass N)`. | 2937–2940, 11158–11160 | ELLIOT input through the existing audited print at the represented classes. |
| `[E.IsElliptic]`, `[NeZero N]`, `f : Newform N 2`, `hf : IsNewformOf E f`, `Lat : PeriodPair`, `hLat : IsLatticeOf E Lat`, `hκ : IsParamScale N f.toCuspForm Lat κ`, and `hgp : GenusPartner E d`. | 1761–1787, 1825–1828, 2404–2410, 8247–8254 | ELLIOT assembly: existing curve, modularity, normalization and genus partner inputs. |
| For the separate rationality reduction: independently chosen maps `q_f : J₀(N) → A_f` and `α : A_f → E` over `ℚ`, and on a width one cusp tail the projective evaluation of `AJ ≫ q_f ≫ α` equal to `weierPt E Lat (κ * eichlerPotential f τ)`. | 1781–1787, 1825–1828 | ELLIOT input for the independent maps; substantial missing comparison theory, for example a computation of their normalized differential and base value. |

## Known issues

- Inherited audit at tex 1784: the cited pair gives the quotient and isogeny part, while the normalized newform statement is covered by Proposition 11.21 in the in-tree Milne audit. The pair does not give the Hecke equality at tex 1788. That audit also records two unused misprints in Conjecture 11.17. These locators were not checked against the primary source here.
- The manuscript's Elkik locator is **UNVERIFIED** against the primary source here. The existing printed input is pointwise torsion; the finite range of the actual cusp classes gives finiteness of the generated subgroup.
- A rational number labels a geometric cusp orbit. Such a label does not give that cusp residue field `ℚ`.
- No additional error was found in the reviewed lines.

## Manuscript check

| Tex | Verdict |
| --- | --- |
| 1779–1784 | Error at 1784, inherited: the cited locator omits the normalized newform statement. |
| 1784–1787 | Gap filled in the preceding run: trivial character identifies the underlying functions of the two newform realizations. |
| 1785–1787 | Gap filled in the preceding run: the fixed model and the chosen period quotient agree on complex points, including at infinity. |
| 1785–1787 | Gap filled: the chord and tangent law is realized on this fixed model over ℚ, with compatibility on complex points. |
| 1781–1787, 1825–1828 | Unverified for the independent maps and their fixed scale cusp tail; no at-scale output supplies these. |
| 2836–2838 | Gap filled at the rational scale given the scheme group law: faithful point evaluation identifies the based morphism, so the Albanese factor applies. |
| 2937–2939 | Gap filled in the preceding runs: the Jacobian cusp classes are the represented geometric point-minus-infinity classes, with finite range. |
| 2940–2942, 11158–11160 | OK as invoked: the existing pointwise torsion print yields a finite subgroup using the cusp orbit factorization. |
| 1825–1828, 7175–7180 | Gap filled at the rational scale given the scheme group law: specialization computes the precise cusp symbol for the weighted comparison. |

## Validation

The imports were built with `lake build`, including the inherited fixed scale comparison. All seven new files passed serial `lake env lean -j1 -DautoImplicit=false` checks. The 61 axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`. The preceding proof files and printed inputs were left unchanged. Per-file results are in `scratch/rc-j0-cusps4/log.md`.
