# Rational Atkin–Lehner action for the (O.7) input

Lean constructs `rationalAtkin hQ : RationalAtkin (X0Branch.model N) hQ`
for every exact divisor of the positive level. The involution has the
pinned complex chart action and squares to the identity. The at-scale
join uses `X0Branch.model N`, which is built on `X0Model.curve N`;
`X0Model3` is not the consumer's model.

The generic producer `genericFibreAtScale` gives the original
`BasedAtkinOnPoints` on that model, at the rational formal cusp and
with the pinned newform sign. It also gives the translated identity
with constant $P(W_Q\infty)$ after arbitrary field extension.
The rational representative of the fixed scale remains an input.
No printed leaf is added. The function field route uses the existing
rational Laurent descent and the smooth proper normalization, so it
needs neither explicit gluing formulas on the normalization nor a new
moduli construction.

## Statements

The declarations are in `ZInQ.Manuscript.RC.AtkinRational`. The
construction and comparisons are ON THE SPOT (c).

| Declaration | Statement and use |
| --- | --- |
| `Coordinates.levelInvariant_of_dvd`, `jqN_mem_of_dvd` | For positive $m\mid N$, the dilated $j(m\tau)$ is invariant at level $N$, and its rational Laurent series belongs to `modularFunctionField N`. The orbit degree bound and rational Laurent descent supply membership. |
| `Matrix.coe_atkin`, `chart_coordinates` | Read off the chosen matrix entries and identify the two transformed generators as $j(Q\tau)$ and $j((N/Q)\tau)$. |
| `FunctionField.fieldGerm_jqN`, `fieldGerm_first` | The rational Laurent elements for $j_m$ and $j$ give the germs of the analytic coordinates at each chart point. |
| `FunctionField.mobius`, `mobius_tendsto`, `pullPuncturedGerm`, `pullGerm` | Möbius map and pointed limit; precomposition homomorphisms on punctured and meromorphic germs. |
| `FunctionField.exists_pullback`, `pullback`, `fieldGerm_pullback` | Existence and construction of the rational function field endomorphism and its compatibility with precomposition on all meromorphic chart germs. |
| `Model.hasValue_pull`, `pullValuation`, `pullValuation_residue` | Precomposition preserves a finite limit and defines the corresponding local ring map commuting with the residue. |
| `Model.spec_to_rat_eq`, `exists_modelMap`, `modelMap_chart` | Uniqueness of maps of affine schemes into $\operatorname{Spec}\mathbf Q$; extension of the generic map; its analytic arc specializes to the prescribed chart point. |
| `Model.exists_transcendental_j`, `jLinePoint_generic`, `exists_dominant_chart` | Some interior parameter has transcendental $j$; it lies over the generic point of the $j$-line and gives a dominant chart map to the rational curve. |
| `Model.ext_model_of_chart`, `modelMap_square`, `rationalAtkin` | Equality on the chart implies equality of maps to a separated target. This gives the square and the original `RationalAtkin` structure. |
| `Infinity.formalClosedPoint`, `infinity_zero_of_pole`, `algebraicParametrizationAtScale_atInfinity` | Constant coefficient reads the formal disc's closed point; the nonzero $q^{-2}$ coefficient forces $P(\infty)=0$ for the fixed at-scale map. |
| `Density.eq_over_rat`, `exp_eq_qpow`, `section_constant_rational` | Unique affine scheme maps to $\operatorname{Spec}\mathbf Q$, the exponential expression for $q^n$, and rationality of a constant chart section via its Laurent expansion. |
| `Density.eq_constant_of_chart` | A morphism over ℚ to a separated scheme that is constant on the complex chart equals the constant morphism through the image of any rational point. |
| `PointReading.ellipticAffineOpen`, `ellipticAffineIso`, `ellipticAffineInclusion`, `range_ellipticAffineInclusion`, `mem_ellipticAffineOpen_iff` | The affine Weierstrass chart, its isomorphism to the spectrum of the coordinate ring and its open immersion, with image the complement of the origin. |
| `PointReading.ellipticAffineLift`, `ellipticAffineLift_fac` | Maps with image in the chart factor through the affine inclusion. |
| `PointReading.affineRingMap`, `affineRingMap_Spec`, `affineRingMap_injective` | Read a map of affine schemes as a ℚ-algebra homomorphism; this inverts `Spec.map` and is faithful. |
| `PointReading.projectiveValue_eq_some_of_affine`, `projectiveValue_affine_spec`, `projectiveValue_eq_zero_iff`, `projectiveValue_eq_of_affine` | Coordinate formulas on the affine chart and the criterion for zero; equality of affine point readings identifies the scheme points. |
| `PointReading.uniq_homs_of_rat_embedding`, `projectiveValue_injective_of_origin`, `projectiveValue_surjective_of_origin` | The residue field of a rational point embeds into ℚ and hence admits at most one map to each field. With a rational origin, the point reading is bijective. |
| `Based.RepresentsDifference`, `based_of_representedDifference` | Compatibility of point subtraction with morphisms to this projective model; given that compatibility, the chart equation gives the original `BasedAtkinOnPoints`. |
| `Reduction.spec_to_rat`, `projectiveOverQ_proper`, `valuative_ext`, `read_spec_affine` | Maps from an affine scheme to $\operatorname{Spec}\mathbf Q$ are unique; the projective structural map is proper; generic restriction to a field extension of a domain detects equality; an affine coordinate evaluation specializes by composition. |
| `Reduction.integralModel_eq_baseChange`, `reducedModel_eq_baseChange`, `projectiveReduction` | For a valuation ring containing ℚ, the integral and residue equations are the base changes of the fixed equation. The good reduction map is additive on those point types. |
| `Reduction.projectiveValue_specialization` | On a map from the spectrum of such a valuation ring to the fixed projective scheme, reading the closed point equals reducing the reading of the generic point. |
| `Difference.representsDifference_of_origin` | With a rational origin, the signed difference of any two morphisms from the modular curve to the fixed projective target is represented, on every field point. |
| `Difference.basedAtkinAtScale` | The original `BasedAtkinOnPoints` for a normalized map with the prescribed chart, with the constructed rational involution and the pinned sign. |
| `Difference.genericFibreAtScale` | Builds the normalized at-scale map and returns the based and translated identities; the formal cusp supplies the rational origin. |
| `Consumer.overRelation_of_dominantPoint`, `overRelationAtScale` | A faithful multiplicative reading at a dominant field point detects the group-valued relation; applied to the normalized formula via the fixed elliptic point reading, it gives the corresponding equation in `Over`. |
| `Consumer.overRelation_baseChange` | Base change preserves the group-valued relation and gives the shape used by the integral specialization theorem. |

## Construction

**ON THE SPOT (c): check the pullbacks in the actual chart.** Put $M=N/Q$.
By `TauCeti.IsAtkinLehnerMatrix.exists_entries`, the chosen matrix $A$
has entries $Qa,b,Nc,Qd$ in row order, with $Qad-Mbc=1$. Then

$$
 A=\begin{pmatrix}a&b\\Mc&Qd\end{pmatrix}
   \begin{pmatrix}Q&0\\0&1\end{pmatrix},\qquad
 \begin{pmatrix}N&0\\0&1\end{pmatrix} A
 = Q\begin{pmatrix}Qa&Mb\\c&d\end{pmatrix}
     \begin{pmatrix}M&0\\0&1\end{pmatrix}.
$$

Both left factors of the non-scalar products are in
$\mathrm{SL}_2(\mathbf Z)$; the scalar $Q$ acts trivially on the upper
half-plane. Thus $j(A\tau)=j(Q\tau)$ and $j(NA\tau)=j(M\tau)$.
This checks the `atkinGL` convention directly. The Laurent orders at
infinity are $-Q$ and $-M$; the literal swap of the original series
is the Fricke case $Q=N$.

**ON THE SPOT (c): build the rational map.** The rational pullback is a ring homomorphism
$\alpha_Q:\mathbf Q(j,j_N)\to\mathbf Q(j,j_N)$ satisfying, for all
$\tau$ and $f$,

$$
 \operatorname{fieldGerm}_{\tau}(\alpha_Q f)
  = (z\mapsto Az)^*\operatorname{fieldGerm}_{A\tau}(f).
$$

The pullback on the right is precomposition of punctured meromorphic
germs. It is well defined because the Möbius map is analytic and
locally invertible. For the two generators, use
`X0Model2.exists_hasSum_meromorphicContinuation` for the elements of
the rational field and `X0Model.hasSum_jN` for the dilations.
Uniqueness of the sum gives equality on a cusp tail. The meromorphic
identity theorem identifies the germs at each interior parameter.
Both images belong to the field by `jqN_mem_of_dvd`, so field
generation extends the substitution to every element. Injectivity
of the meromorphic germ embeddings and of Möbius precomposition
ensures that a nonzero denominator remains nonzero. The germ comparison uses the existing continuation API.

Extend the generic map using `Scheme.exists_hom_of_valuationRing_stalk`.
The stalk condition follows from `smooth_curve_valuation_stalk` and
`ParamAtScale.model_dimension`; the target is proper by
`X0Model.proper`. For the chart condition, pull back the analytic
arc at $A\tau$ along precomposition on valuation rings of finite
germs. This arc and the analytic arc at $\tau$ followed by the
extended map agree generically by the displayed compatibility.
Uniqueness in `X0Model.existsUnique_specialization` identifies them
over the valuation ring. Precomposition preserves the finite limit,
so the closed complex points agree. This step compares branches
of the normalization even over singular points of the plane equation.

For the square, `AtkinPin.atkinInterior_involutive` gives the
identity on the chart. To show the chart is dense over $\mathbf Q$,
choose $\tau$ with $j(\tau)$ transcendental: the range of $j$ is
connected and nonconstant by its pole, so it cannot be contained in
the countable, totally disconnected set of algebraic numbers.
By `X0Model2.complexPoint_jProjection` this point lies over the
generic point of the $j$-line. The $j$-projection is finite, hence
closed, so the point on the integral curve cannot be closed. It
must be the generic point. The map $\operatorname{Spec}\mathbf C\to
X$ is therefore dominant over $\mathbf Q$. Apply
`ext_of_isDominant_of_isSeparated` on the reduced source. This
supplies the fixed `RationalAtkin (X0Branch.model N) hQ`,
with its original fields. The square also shows that the realized
function field pullback is an automorphism.

**ON THE SPOT (c): represent the signed difference.** Write $P$ for
the reading after $\pi$ and $e=$ `(signUnit f hχ hQ : ℤ)`. Take the
difference $P(W_Q\eta)-[e]P(\eta)$ at the generic point. The affine
coordinates, or the rational origin if it is zero, give a point of
the fixed projective target. Extend that point to a morphism $D$
by properness and the valuation stalks of the modular curve.

At a stalk of the curve, all rational coefficients are integral and
the discriminant is a unit. Reading the reduction of a scheme point
agrees with the existing good reduction homomorphism: if the generic
point is the origin, separatedness identifies its extension with the
constant origin; if its affine $x$ is integral, then so is $y$, and
the affine lift specializes by reducing both coordinates; if $x$ has
a pole, specialization into the affine chart is impossible. This
proves the comparison on the fixed `Proj` without constructing a
scheme group law on a product. Additivity then gives the required
reading of $D$ over each residue field. Every field point factors
through its residue field, so `projectiveValue_map` gives the same
reading after extension.

**ON THE SPOT (c): descend the based identity.** The pinned identity
and faithfulness of the elliptic point reading make $D$ constant on
the complex chart. Take an affine neighborhood of that common value
and pull back its regular functions. Their rational Laurent expansions
are constant by uniqueness of the expansions along the chart, so
the constant values are rational. The coordinate ring map therefore
gives a rational constant point of the separated target. The rational
modular curve is reduced and the chart contains a dominant field point.
Equality there identifies $D$ with the rational constant morphism on
the whole curve.

Evaluating at $b=\texttt{infinityPoint}$ identifies the constant as
$P(W_Qb)-[e]P(b)$. Evaluating again after scalar extension and
subtracting gives exactly
`BasedAtkinOnPoints X W π hπ b e`. For the normalized conclusion
of `translatedAtkinAtInfinity`, one also needs $P(b)=0$ on this
same $\pi$. A direct formal proof uses the nonzero $q^{-2}$
coefficient $\kappa^{-2}$ of $x\circ\pi$. If the cusp mapped into the
affine chart $Z\ne0$, the $x$-coordinate would pull back to
$\mathbf Q[[q]]$ along `X0Model.formalQArc`, contradicting that
coefficient. Therefore the cusp maps to the projective identity.
The proof retains the generic coordinate witness in
`dominant_morphism_of_classification` to compare to the formal arc.

## Generic input and remaining hypotheses

The producer, at `N = newformLevel (Ecurve ℓ)`, takes
ellipticity, positive level, the fixed normalized form data
`f hχ hf`, `Lat hLat κ hκ`, a rational representative of `κ`,
and `hQ : Q ∥ N`. It returns the pinned chart's dominant $\pi$
over $\mathbf Q$, the rational involution with its chart,
`BasedAtkinOnPoints` at `infinityPoint` with
`e := (signUnit f hχ hQ : ℤ)`, and the normalized translated
identity over every field. No Atkin–Lehner hypothesis is in this
statement. For $Q=p^{v_p(N)}$ the sign is
`(wNew f hχ p : ℤ)` by definition. Take `f := F.form` and `hχ := F.trivial` for the consumer newform. Its
pointwise conclusion is `ha` of `AtkinPin.pinned_atkin_quotient_of_specialization`.
For the morphism consumer, `overRelationAtScale` gives
$W\mathbin{\gg}\pi=\pi^e\cdot t$ in `Over`, with $t$ read as
the constant moved cusp, once the group model is compared to the
fixed projective equation. Apply `overRelation_baseChange` along
$\operatorname{Spec} K\to\operatorname{Spec}\mathbf Q$. Identification
with the generic fibres of the integral maps gives `hgen` of
`GoodReduction.atkinQuotient_of_integralRelation`. For the point
consumer, the separate `BasedSpecialization` hypothesis remains.

| Remaining input | Reduction or reason it remains |
| --- | --- |
| Ellipticity of `Ecurve ℓ` and $N>0$ | Properties of the concrete curve and stage. `StageKummer.positiveLevel` supplies stage positivity. No printed input. |
| Newform `f` at the actual conductor, trivial character `hχ`, Fourier agreement `hf` | Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises* (2001), Theorem A and introduction (locators **UNVERIFIED**); conductor comparison via Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert* (1986), local conductor theorem, number **UNVERIFIED**. The existing `ModularNewform` and `AtkinPin.consumerNewform` identify the form used by the consumer. |
| Chosen `Lat` and `hLat : IsLatticeOf E Lat` | Complex uniformization, e.g. Silverman, *The Arithmetic of Elliptic Curves* (2009), VI.5, locator **UNVERIFIED**. The lattice also has to be the one chosen for this normalization. |
| `κ` and `hκ : IsParamScale N f Lat κ` | Pull back the invariant differential along the manuscript's based map and integrate at this scale. For the modular quotient see Shimura, *On the factors of the jacobian variety of a modular function field* (1973), theorem number **UNVERIFIED**. The nonzero scale and its compatibility with the chosen normalization are part of the input. |
| `hr : ∃ c : ℚ, (c : ℂ) = κ` | Comparing rational differentials gives the scalar for a specified rational map. It does not identify an independently supplied scale. This input is not obtained from `ParamJoin/AtScale`. |
| `hQ : Q ∥ N` | Elementary exact-divisor arithmetic; at the full prime power use `TauCeti.Nat.isExactDivisor_primePow`. Atkin–Lehner, *Hecke operators on Γ₀(m)* (1970), number **UNVERIFIED**, is used only via the existing Lean newform eigenrelation. The rational action is constructed above. |
| Identifications of the generic fibres and compatibility of the group model's field reading | Model comparison for the integral consumer. An elliptic Weierstrass model's regular group law is standard (Silverman 2009, III.3, locator **UNVERIFIED**); a theorem about some group model does not identify the two particular maps and the section used in the consumer. |
| `BasedSpecialization`, torsion multiplier, weighted row | Separate inputs. Good modular reduction reduces to Deligne–Rapoport, *Les schémas de modules de courbes elliptiques* (1973), number **UNVERIFIED**; extension uses the Néron mapping property in Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), locator **UNVERIFIED**. The manuscript cites Manin–Drinfeld through Elkik, *Le théorème de modularité de Wiles* (1996), p. 59 (locator **UNVERIFIED**). These claims do not identify the actual weighted coefficient. |

The valuative comparison used inside the rational proof reuses the
already formalized good reduction homomorphism in
`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/GoodReduction.lean`.
See Silverman (2009), VII.2.1 (locator **UNVERIFIED**), and Bosma and
Lenstra, *Complete systems of two addition laws for elliptic curves*
(1995), theorem number **UNVERIFIED**. The calculation translating
that homomorphism to scheme specialization is proved here.

The focused Lake build covers every module listed above. The
declarations' `#print axioms` outputs use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Known issues

- Inherited: the Milne locators at tex 1784–1788 do not state the
  normalized-newform and good Hecke claims. See
  `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean`.
- Inherited: the earlier (O.7) audit flags the level-one scope of
  the cited Jetchev–Kane comparison at tex 8468–8474. The source
  locators for these inherited issues were not independently checked.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1779–1783: take the curve's actual conductor and newform. | OK |
| 1784–1788: the Milne locators for the normalized form and Hecke claim. | unverified (inherited citation scope above) |
| 1785–1787: base the rational map at infinity. | gap filled (formal cusp comparison) |
| 1825–1828: use the same fixed period scale. | OK |
| 2937–2942: kill the image of the cuspidal classes. | unverified (outside this work) |
| 2943–2944: construct the rational action used by the formula. | gap filled (matrix check, Laurent membership and rational extension) |
| 2943–2946: descend the translated identity to every field point. | gap filled |
| 8468–8474: cite Jetchev–Kane for the full-level supersingular comparison. | unverified (inherited citation scope above) |
| 8476–8479: specialize at the good prime. | unverified (outside this work) |
| 8487–8489: signed identity on the generic fibre with the moved cusp constant. | gap filled |
| 8487–8489: identify the integral extension and kill the specialized constant. | unverified (outside this work) |
| 9101–9113: generic Atkin–Lehner input to the unaveraged comparison. | gap filled |
| 9331–9341: match orientation reversal and the local norm weight with the sign on reduced values. | unverified (specialization and weights outside this work) |
