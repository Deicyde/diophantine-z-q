# Rational fibre of the pinned short-level quotient

The scheme-theoretic generic fibre of each admissible `Pinned.Y0Level` is the single quotient `Y0Rational` over the rationals. The comparison preserves the actual first j-coordinate. The rational quotient is normal and finite over the affine j-line, and each detector fibre has the pinned geometric pair reading. Its localization at the generic point of the j-line is a finite-dimensional reduced algebra over `LeafModCurves.Qj`, and the localization map is injective.

The open comparison at tex 8476–8478 remains pending. The next step is to establish that the pinned pair reading over the indeterminate j identifies the geometric points with the cyclic subgroups of the actual `Ej`, equivariantly under Galois. This is the input for descending the genuine Vélu quotient invariant and proving integrality. `GenericFibreComparison` remains uninstantiated.

## Checked declarations

The modules are in `ZInQKernel/Contrib/OneProof/RC/ModelGeneric`.

All eleven modules passed the combined serialized Lake build. The 56 axiom checks contain only `propext`, `Classical.choice` and `Quot.sound`.

**ON THE SPOT (c).** The comparison between the formal short presentations is scalar extension on the two coefficients, the marked point and the inverse discriminant. The polynomial presentation then identifies the weights, and naturality of multiplication on the marked point identifies the unit actions. The imported scalar extension of invariants yields the required quotient equivalence. Faithful localization over the j-line uses the short form of the existing `Ej` to witness the indeterminate j.

| Short locus and marked cover declaration | Statement and role |
| --- | --- |
| `Algebra (LocalIntegers ell) ℚ`, `rational_isFractionRing` | The canonical map from the detector's localization at the prime `ell` exhibits the rationals as its fraction field. |
| `shortBaseMap`, `shortBaseMap_polynomial` | For an algebra `R → B`, the map `ShortBase R →+* ShortBase B` acts by coefficient extension on the two-variable polynomial subring. It equips the short loci with compatible algebra and scalar tower structures. |
| `shortBase_isPushout` | The square with corners `R`, `B`, `ShortBase R`, and `ShortBase B` is a pushout of algebras. The polynomial and discriminant-localization stages both commute with base change. |
| `shortFamily_map_shortBaseMap` | The universal short Weierstrass equation maps to the universal short equation over `B`. This is the curve input to exact-order base change. |
| `shortEquation_map_coefficients`, `shortDiscriminant_map_coefficients`, `shortDiscriminant_localization` | The auxiliary lemmas map the Weierstrass coefficients and the discriminant on polynomial rings. The target short base is the localization at that mapped discriminant. |
| `exactOrderCurveCongr`, `shortCoverCoefficientBaseChange` | Transport across equality of elliptic equations combines with the existing exact-order comparison to give the algebra equivalence after extension along `ShortBase R → ShortBase B`. |
| `shortCoverBaseChange`, `shortCoverBaseChange_tmul_one`, `shortCoverCoefficientBaseChange_algebraMap` | The marked short cover over `B` is the base change of the cover over `R`. The equivalence sends `1 ⊗ x` through the short-locus pushout and agrees with the short coefficient map on coefficients. |
| `exactOrderCurveCongr_xy`, `exactOrderCurveCongr_units`, `shortCoverCoefficientBaseChange_xy`, `shortDiscriminant_mul_inv` | Transport preserves the marked coordinates and unit action. The inverse discriminant is characterized by its product with the discriminant. |
| `shortCoverBaseChange_coordinates`, `shortCoverBaseChange_presentation`, `shortCoverBaseChange_mem` | The comparison sends the five named coordinates to their counterparts over the new base. It thus preserves the polynomial presentation and the components induced by the weights. |
| `shortCoverCoefficientBaseChange_units`, `shortCoverBaseChange_units` | Under the coefficient-domain hypotheses, the geometric multiplication by units commutes with the comparison on tensors. |
| `j_congr`, `shortCoverBaseChange_j` | The comparison takes the j-invariant of the source equation to the j-invariant of the scalar-extended equation. |

| Rational declaration | Statement and role |
| --- | --- |
| `rationalLevel_isUnit`, `rationalCover` | A nonzero level is invertible in `ShortBase ℚ`. The marked cover is the existing exact-order algebra of the universal short equation over that ring. |
| `rationalGrading`, `rationalGradedAlgebra` | The five coordinate weights define the internal grading on the rational cover. |
| `rationalAction`, `rationalAction_comm`, `rationalAction_preserves` | The geometric change-of-generator action of `(ZMod N)ˣ` commutes with rational scalars and preserves each graded component. |
| `Y0RationalAlgebra`, `Y0Rational`, `Y0RationalInclusion` | For `2 ≤ N`, the detector-independent ring is the degree-zero part of the fixed subalgebra. Its spectrum is over `Spec ℚ`, and the ring embeds in the marked cover. |
| `rationalJ_mem`, `Y0RationalJ`, `Y0RationalJMap` | The j-invariant of the universal source equation has weight zero and is fixed by the change of generator. It is the image of the polynomial coordinate in the map from `Polynomial ℚ`. |
| `Y0RationalJMap_finite` | The rational ring is finite as a module over the polynomial ring via that j-map, using the discriminant-one slice. |
| `rationalCover_regular`, `Y0RationalAlgebra_normal` | The exact-order cover is smooth over the rationals and hence regular. Each prime localization of the degree-zero invariant ring is a normal domain, by the imported retract argument. |
| `shortBase_aeval_j_injective`, `Y0RationalAlgebra_j_torsionFree` | The short coefficient ring's j-map is injective, witnessed by the short form of `LeafModCurves.Ej`, which has indeterminate j. Flatness of the marked cover over the coefficient ring then gives torsion-freeness of the rational quotient over `Polynomial ℚ`. |
| `Y0RationalGenericJ`, `Y0RationalGenericJInclusion` | Base change the rational quotient along the actual j-map to the fraction field `LeafModCurves.Qj` of the affine j-line. The inclusion is the canonical map of this localization. |
| `Y0RationalGenericJ_finite`, `Y0RationalGenericJInclusion_injective`, `Y0RationalGenericJ_reduced` | After this localization the algebra is finite dimensional over `Qj` and reduced, and the inclusion is injective. This is the algebra for the pending Galois descent of the quotient invariant. |

| `DetectorFibre` declaration | Statement and role |
| --- | --- |
| `detectorRationalPoint`, `detectorFibreAlgebra`, `detectorFibreIso` | For prime `ell ≥ 5`, `2 ≤ N` and `¬ ell ∣ N * N.totient`, the generic pullback of `Pinned.Y0Level` along `Spec ℚ → Spec (LocalIntegers ell)` is the spectrum of its rational scalar extension, as a scheme over `ℚ`. |
| `detectorFibrePoints` | For an algebraically closed `ℚ`-field with the compatible detector algebra structure, its geometric points are `PairClasses k N` via restriction and `Pinned.Y0LevelPoints`. |
| `detectorFibreJ`, `detectorFibre_normal` | The first j-coordinate is the image of `Pinned.Y0LevelJ` under scalar extension. The prime localizations are normal domains. |
| `degreeZeroEquiv`, `Y0RationalBaseChange` | A graded algebra equivalence restricts to degree zero. Composing `Pinned.levelQuotientBaseChange` with the graded and equivariant comparison of the covers identifies each detector tensor algebra with `Y0RationalAlgebra`. |
| `Y0RationalBaseChange_j` | That algebra equivalence sends `detectorFibreJ` to `Y0RationalJ`. The map to the actual affine j-line is common to all admissible detectors. |
| `Y0RationalFibreIso` | For every admissible detector, the scheme-theoretic generic pullback of `Pinned.Y0Level` is isomorphic to `Y0Rational` in schemes over `Spec ℚ`. |

## Remaining work and standard reductions

The inherited tier rows are reproduced below.

| Tier | Smallest faithful statement | Reduction and reference |
| --- | --- | --- |
| Substantial generic comparison | An isomorphism of the rational fibre with the finite chart of `X0Branch.model N` respecting the actual $j(E),j(E/C)$, cyclic subgroup, $W_Q$, $T_q$ and fixed parametrization. | Compare the normal affine charts over $\mathbb Q[j]$ using the function field generated by the two $j$-functions. Diamond and Shurman, *A First Course in Modular Forms*, 2005, §7.5 UNVERIFIED. `GenericFibreComparison` remains uninstantiated. The pinned $j$ and pair reading are available. The missing data include an independent reading of the quotient $j(E/C)$ and the actual operators and fixed parametrization on the two charts. The complex branch reading needs the identification between the finite chart of `X0Branch.model N` and the complex classes of cyclic pairs. The generic source also needs the actual open immersion into the compact curve. |
| Small after generic comparison | Extend the fixed parametrization from the identified generic open to the integral open with target the Néron model. | The Néron mapping property. Bosch, Lütkebohmert and Raynaud, *Néron Models*, 1990, §1.2 Definition 1 and §1.4 UNVERIFIED. |
| Medium pointwise operators | Over the same strict henselian DVR, the prime-to-residue-characteristic torsion kernels lift uniquely and quotient isogenies and level transport specialize to the correct coarse points. Match the two operations with the fixed generic ones. | Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, 1985, §2.4 UNVERIFIED. Vélu, *Isogénies entre courbes elliptiques*, 1971, formula locator UNVERIFIED. The pointwise lift and specialization comparison is **ON THE SPOT (c)** as a reduction of the manuscript’s global operator identity. Atkin and Lehner, *Hecke operators on Γ₀(m)*, 1970, §4 UNVERIFIED. |
| Downstream same-place comparison | Identify the supersingular pairs and their Frobenius with the actual adelic labels. Identify the reductions of the actual CM lifts and of the fixed parametrization at the same chosen place. | The manuscript invokes Jetchev–Kane at tex 8473–8474 and Cornut–Jetchev, *Liftings of reduction maps for quaternion algebras*, 2010, §§4.9–4.10 UNVERIFIED. The exact same-place comparison still needs a checked refereed locator. |

### Algebraic comparison

The fixed finite chart is the preimage of the finite j-line in the normalization of the projective j-line in `modularFunctionField N`. The excluded points are the cusps, i.e. the points over $j=\infty$. `NormalModel.f.normalizationObjIso` on chart zero identifies its sections with the integral closure over the affine line. The first coordinate is pinned by `X0Model.jCoordinate_X`.

The existing leaf is `CyclicQuotientJBijOn` in `CloudB2X0Transitive/Bridge.lean`. Its exact statement is the universe-zero specialization of the vendored Anthropic FLT theorem `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`. For an algebraically closed extension $L/K$, an elliptic equation $E/L$ with $j(E)$ transcendental over $K$, and $N$ nonzero in $L$, the map $C\mapsto E.\texttt{cyclicQuotientJ}(C,N)$ is a bijection from the cyclic subgroups of order $N$ to the roots of the specialization $\Phi_N(X,j(E))$ of `ModularPolynomialData N`. The reduction `x0Transitive_of_cyclicQuotientJBijOn` takes this as a hypothesis. The pinned tree includes the later full proof `FltCqj2.cyclicQuotientJBijOn_proof`, recorded in `docs/research/flt-cqj2.md`. Any consumer here retains the explicit hypothesis. Classical statements are Lang, *Elliptic Functions*, 1987, Ch. 5 §2 Thm. 3 UNVERIFIED, and Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, 1994, Ch. II modular-polynomial discussion, locator UNVERIFIED. The formula for the actual quotient reduces to Vélu, *Isogénies entre courbes elliptiques*, 1971, formula locator UNVERIFIED, and Silverman, *The Arithmetic of Elliptic Curves*, 2009, III.4.12 UNVERIFIED.

**ON THE SPOT (c).** Put $K=\mathbb Q(j)$ and $B_K=K\otimes_{\mathbb Q[j]} B$, the checked `Y0RationalGenericJ` for the named rational quotient $B$ with its actual j-map. The smallest remaining comparison on this side is that the finite reduced $K$-algebra $B_K$, after extension to $\bar K$, has its geometric points equivariantly identified with the cyclic subgroups of the actual $E_j$, through the pinned pair reading. The identification must commute with all $K$-automorphisms of $\bar K$. The source equation is identified with $E_j$ by the short-form/isomorphism criterion for equal j. At indeterminate j, its automorphism group acts trivially on cyclic subgroups, so transport is independent of the isomorphism.

More precisely, the required map sends $x\in\operatorname{Hom}_{K\text{-alg}}(B_K,\bar K)$ to the image of the subgroup in the pinned pair of $x|_B$, under any isomorphism of its source curve with $E_j\otimes_K\bar K$. Prove that it is a bijection onto $\{C\le E_j(\bar K)\mid C\text{ cyclic},\ |C|=N\}$ and that it sends $\sigma\circ x$ to $\sigma C$ for all $\sigma\in\operatorname{Aut}_K(\bar K)$. This uses the j-coordinate to restrict the reading to the fibre over the indeterminate j.

**ON THE SPOT (c).** In the split algebra of geometric points take the tuple whose value at the point represented by $(E_j,C)$ is $j(E_j/C)$ from the actual iterated Vélu equation. Each step quotients by the prime-order part of the kernel and transports the remaining subgroup using the step's quotient formulas. The final quotient invariant is $c_4^3/\Delta$ of that equation. Galois equivariance descends the tuple to $B_K$. Under the bijection hypothesis the tuple distinguishes all geometric points and its values are exactly the roots of $\Phi_N(X,j)$. Since the polynomial is monic and irreducible, the tuple generates $B_K$, which is then a field of degree $\psi(N)$. The argument over an algebraically closed ground-field extension uses the corresponding specialization over its rational function field to give geometric irreducibility. Normality and the monic equation give the quotient coordinate in $B$.

The vendor tree proves `ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi` and `ModularCurve.ModularPolynomialData.minpoly_jqN_eq`, with `ModularCurve.phiIrreducible_all` and `ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero`. These identify the prescribed Laurent-series root of the same minimal polynomial using the existing $j\mapsto j_q$. A separate Tate-curve evaluation is unnecessary for this algebraic route. The two normal finite chart rings then identify as integral closures. This uses the definition and uniqueness of integral closure, Atiyah and Macdonald, *Introduction to Commutative Algebra*, 1969, Chapter 5 locators UNVERIFIED. No new printed-form leaf was introduced.

The function-field isomorphism must send the descended Vélu invariant to `ModularCurve.jqN N`. The integral closure isomorphism gives the affine open immersion over the same j-line, and the established complex branch of the fixed curve is the test for the pair interpretation of that immersion. A pair reading at arbitrary normalized points requires more than uniqueness on the locus where the two j-coordinates distinguish the pairs.

| Remaining comparison | Standard reduction |
| --- | --- |
| Equivariant generic pair reading | Prove evaluation at the actual first j agrees with the source curve of the pinned pair and that the pinned equivalence is natural under field automorphisms. Then use the imported short stabilizer result and the equal-j classification of curves, Silverman, *The Arithmetic of Elliptic Curves*, 2009, III.1.4 UNVERIFIED. The equivariance for the pinned ring is substantial Lean glue, with the precise equivariance statement above. |
| Integrality and the actual quotient coordinate | The finite separable algebra argument above uses `CyclicQuotientJBijOn` explicitly for the root locus, its existing transitivity reduction for the field property, and Vélu for the actual coordinate. Proving descent and generation on the pinned ring is substantial Lean work even with the vendor results. It needs no additional modular-curve print. |
| Isomorphism of function fields and open immersion | After the quotient coordinate generates, compare the two roots by the existing minimal polynomial theorems. Apply uniqueness of integral closure over the actual j-line, Atiyah and Macdonald, 1969, Ch. 5 UNVERIFIED. |
| Pair reading everywhere on the fixed finite chart | The quotient coordinate singles out the cyclic pair wherever it is unique. At collisions of the two coordinates, use the normal chart, with the branches distinguished by the moduli reading. Match the fixed complex point of $\tau$ with $(\mathbb C/\langle1,\tau\rangle,\langle1/N\rangle)$. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, Prop. 6.9 and Thm. 6.23 UNVERIFIED. Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, 1985, Chs. 8 and 13 UNVERIFIED. Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*, 1973, VI UNVERIFIED. |
| Pointwise exact-divisor and good Hecke operators | The lattice or quotient-isogeny readings are the actual $(E/C_Q,(E[Q]+C)/C_Q)$ and the multiset of $(E/D,\operatorname{im} C)$ over the $p+1$ order-$p$ subgroups. Check the actions against the fixed morphism and correspondence, preserving neighbour multiplicities. Atkin and Lehner, *Hecke operators on Γ₀(m)*, 1970, §4 UNVERIFIED. Katz–Mazur, 1985, §2.4 UNVERIFIED. |
| Fixed parametrization | Restrict the fixed parametrization along the open immersion and define the level value by transporting it through the comparison. The level model has no independent parametrization. This is ON THE SPOT (c). |

## GoodRow and the Néron task

The open comparison supplies `GoodRow.source`. Its equality on fixed Atkin–Lehner readings supplies the generic comparison used by `W_generic`. These fields remain pending. After the identification the composite with the fixed rational parametrization is the morphism to extend using the Néron mapping property on the smooth pinned open. The scope of this comparison ends on the generic fibre.

## Known issues

- The pinned base contains `X0Branch.model` but has no `RC/AtkinRational` modules. The refreshed `origin/wip/rc-atkin-rational2` ref has `rationalAtkin hQ` on exactly that model. The fixed morphism comparison needs that implementation to be available at the build base.
- The inherited Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims used there.
- Jetchev–Kane at tex 8468–8474 omits level one. The reviewer specifies Ribet, *On modular representations of Gal(ℚ̅/ℚ) arising from modular forms*, 1990, Proposition 3.3 and surrounding discussion UNVERIFIED.

## Manuscript check

| TeX lines | Verdict | Step |
| --- | --- | --- |
| 8366–8368 | OK | The finite exclusions allow the detector hypotheses for the pinned construction. |
| 8468–8474 | gap filled | The imported pinned model supplies the geometric coarse pair reading. |
| 8473–8474 | unverified | Identification of the supersingular pairs with the actual adelic labels remains pending. |
| 8476–8478 | gap filled | The imported smooth pinned open has its coarse point reading. |
| 8476–8478 | gap filled | The rational base change of each admissible detector model is the same quotient over the actual j-line. |
| 8476–8478 | unverified | Identification of that open with the fixed rational modular curve remains pending. |
| 8478–8479 | unverified | The extension of the fixed parametrization remains pending. |
| 8479–8487 | unverified | Comparison with the fixed Hecke and Atkin–Lehner operators remains pending. |
| 8487–8492 | unverified | Frobenius agreement with the uniformizer on the actual labels remains pending. |
| 9101–9113 | unverified | The unaveraged (O.7) comparison uses the actual reduced values. |
| 9265–9291 | unverified | The CM comparison uses the actual lifts at the chosen place of (O.2). |
