# Prime branch families on the fixed standard model

`BShFamily.bShStandardModel_proof` proves the unchanged
`R16Thm1.BShStandardModel` GLUE row. `BShFamily.heckeJ1DS_proof` proves
the unchanged `AfTateLam.HeckeJ1DS`. The construction is ON THE SPOT
(provenance (c)). It adds no leaf or fold.

The bridge between Shimura's standard model and the kernel's model is in
neither the manuscript nor its citations. Shimura's rational operators on
his own model do not by themselves identify the two coordinates or the
operators on the arbitrary model specified by the fixed Lean row. See
[r16-thm1b.md](r16-thm1b.md) and [bsh-traces.md](bsh-traces.md).

## ON THE SPOT (provenance (c)): splitting and the kernel index

Write $K=\mathbb Q(X)$. Use the coefficients $(-G/4,-G/4)$, with
$G=27j_X/(j_X-1728)$, and the marked abscissa
$x=46656t_X/(j_X-1728)$. Over the complex lattice these are obtained
by scaling abscissas by $g_2/g_3$. This normalization is used in
punctured germs: the denominators can vanish at the center.

Every analytic torsion section needed here is an integral change of basis
of the section (1/p), up to an original period. For a nonzero
multiple (k) of a triangular generator, use a matrix with bottom row
((k,p+ki)). Its entries are coprime since (0<k<p) and (p) is
prime. For a horizontal section choose a bottom row congruent to
((0,k)) modulo (p). The quotient of the two Eisenstein series
times the holomorphic Weierstrass value at (1/p), composed with the
Möbius transformation, gives the meromorphic section. The old coset
enumerations and the division polynomial root comparison exhaust the
pointwise roots.

One can pass this exhaustion to a splitting statement without a simple
root count. Normalize the division polynomial to be monic. At a generic
parameter it divides a high enough power of the product of all displayed
linear factors: each root's multiplicity is bounded by its degree.
The remainder of this product power upon monic division commutes with
specialization, so its coefficients vanish in the punctured germs.
The local polynomial therefore divides a split polynomial. This
argument also covers the case of repeated roots.
The generic field $L$ is the splitting field of the unscaled
division polynomial. Scaling by a nonzero constant leaves the
roots and their splitting field unchanged; the monic normalization
is used for the remainder argument.

For the kernel index, use the multiset of the normalized x-coordinates of
the nonzero points of a cyclic kernel. Multiplication is computed by
(Phi_n/Psi_n^2). Changing a generator permutes its nonzero residues
modulo (p), so the multiset is independent of the generator. Distinct
directions have no nonzero sections with the same x-coordinate: such
equality would imply equality of the lattice classes up to sign. The
weight of an abscissa is two for a pair of opposite points and one for
the nonzero point of an order two kernel. These are the weights in
the short Vélu formulas; the polynomial's root multiplicities are
irrelevant to the index.

When (p\mid N), the normalized abscissa of the multiple (N/p) of
the mark is the abscissa of the horizontal section (1/p). Exclude its
cluster. When (p\nmid N), no cluster is excluded. The test and the
weighted cluster formation use only expressions over the base field,
so they commute with field automorphisms.

## ON THE SPOT (provenance (c)): marked quotients and descent

In the local splitting field comparison, each embedding into the
meromorphic germ field takes the weighted clusters to the analytic
ones. Since the normalized coefficients and mark already have their
prescribed germs, the same three short sums compute the quotient pair
in both fields. The previously checked lattice formulas identify both
coordinates with the triangular pullback or, at good primes, the
horizontal pullback including the specified diamond. Sending both
components through the same embedding is essential.

A match of both generators in one germ ring identifies the integral
polynomial relations in both directions by injectivity of the field
maps. The pair therefore defines an embedding of (K).
An automorphism permutes the kernels and their pairs, so it permutes
these embeddings by field generation. The prime trace theorem descends
and specializes the sum, with the same permutation for both coordinates
and with one entry per kernel even if quotient pairs coincide.
The standard-model assembly then gives the claimed Hecke and diamond
operators.

The offline Lake build of `BShFamily` and `OneProof.Discharges` passed.
All 74 new theorem scans use only `propext`, `Classical.choice`, and
`Quot.sound`. The focused check in
[`scratch/bsh-family/DischargesFocused.lean`](../../scratch/bsh-family/DischargesFocused.lean)
reported:

```text
DISCHARGES [bShStandardModel] by BShFamily.bShStandardModel_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
```

The same check also reports the predecessor's conditional
`bShStandardModel_of_primeTraces`; the new proof supplies its prime
traces. The initial prerequisite build breached the single-process
rule; it was interrupted. The successful build and focused check ran
with an exclusive compiler lock and the prescribed load and memory checks.

## Known issues

- The prior page reading records a typo in Shimura's sentence about
  coefficient conjugates before clause (iv). The eigenvalue should
  multiply the conjugate form. The issue is outside the rational
  operator comparison used here.
- The printed Euler identity is a total product over embeddings. The
  identification of the constituent at the specified embedding requires
  a separate representation argument.
- Vélu's formulas, Diamond–Shurman §§6.3 and 7.9, and Shimura 1971 §7.2
  are background. These section numbers are UNVERIFIED. The construction
  does not use them as new cited inputs.
- The pointwise Weber formula switches normalization at exceptional
  parameters. The argument uses punctured germs of the generic
  coordinates, which are the quantities in the predecessor's fixed
  comparison.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L768, passage to the primitive newform | unverified | The twisting and primitive normalization are outside this proof. |
| L768–770, Fricke stability | unverified | The preceding audit checked the implication conditional on the coefficient conjugates being newforms. This proof does not read Li's page or use the Fricke proviso. |
| L770–771, rational quotient and its Hecke operators | OK | The prior page reading verifies this on Shimura's own standard model. |
| L770–771, comparison on the fixed model | gap filled | The manuscript and its citations do not compare the fixed model with Shimura's. The prime family supplies the two simultaneous coordinate matches and gives the fixed Hecke action in Lean. |
| L771, Euler identity | OK | The prior page reading verifies the total identity under the proviso. |
| L771–772, fixed constituent | unverified | The total identity alone does not select a coefficient embedding. This run does not prove that separate step. |
| L773, identification with the cohomological dual | unverified | The representation dictionary is outside this construction. |
| L11053–11057 | OK | These lines identify Shimura's article, the cited theorem, and its DOI. |

## Lean statements

The names are in `BShFamily`. The table follows the dependency order.

| Theorem | Statement |
| --- | --- |
| `dvd_prod_pow_of_exhaustion` | A nonzero polynomial over an algebraically closed field with roots in a finite family divides the product of the family's linear factors raised to its degree bound. |
| `splits_of_eventually_exhaustion` | A monic polynomial with coefficients and candidate roots in a field of germs splits if its chosen monic representatives eventually exhaust the pointwise roots in an algebraically closed field. |
| `factor_ne` | The Möbius denominator is nonzero on the upper half-plane. |
| `coe_smul_eq_mobius` | The complex Möbius expression computes the integral determinant one action on parameters. |
| `scale_smul` | Multiplying the transformed lattice by that denominator gives the original lattice. |
| `mobius_analyticAt` | The Möbius expression is analytic at every upper half-plane parameter. |
| `normX_period` | Adding an original period preserves the normalized abscissa. |
| `normX_scale_smul` | The homothety preserves the normalized abscissa with its argument scaled. |
| `mobiusX_meromorphicAt` | The reparametrized normalized mark at level at least two is meromorphic. |
| `mobiusX_eq_normX` | The reparametrized normalized mark is the normalized abscissa at its image under the lattice homothety. |
| `exists_matrix` | Each nonzero multiple of a prime line's generator is a transported level (p) mark modulo the original lattice. |
| `exists_torsion_section` | Each such torsion section defines a meromorphic germ at every parameter. |
| `representative_eq` | A prime coset representative is the negative of the corresponding multiple of the line's generator. |
| `multiple_notMem` | Each displayed nonzero multiple is outside the original lattice. |
| `multiple_killed` | Multiplication by the prime takes each displayed multiple to an original period. |
| `exists_normX_of_torsion` | Every nonzero lattice class killed by the prime has one of the displayed normalized abscissas. |
| `eval_division_eq_zero_iff` | At a generic parameter the displayed abscissas are exactly the division roots. |
| `restrict_eq_coe` | Restriction of a representative to the upper half-plane represents the restricted germ. |
| `restrict_punctured_injective` | Restriction to the upper half-plane detects punctured germ equality. |
| `restrict_div` | An eventually nonzero representative denominator allows pointwise division in the restricted germ. |
| `restrict_eventually_ne_zero` | A nonzero meromorphic germ has eventually nonzero values in every representative. |
| `restrict_div_eq` | Restriction preserves pointwise germ division, including the zero-denominator case. |
| `eventually_good` | Both tests for the generic normalization hold in every punctured neighborhood. |
| `map_shortModel` | Mapping the two defining coefficients to another ring maps the short model. |
| `shortModel_quarter` | Using one quarter in the function-ring formula gives the normalized short field model. |
| `map_division` | Base change commutes with the monic normalization of the division polynomial. |
| `division_natDegree_le` | The normalized division polynomial has degree at most (p^2-1). |
| `division_monic` | The normalized division polynomial is monic when the supplied multiplier is the inverse of (p). |
| `division_eval_eq_zero` | The monic normalization does not change the roots. |
| `modelG_pointwise` | The parameter $G$ evaluates to $g_2^3/g_3^2$ where $g_3 \ne 0$. |
| `modelX_pointwise` | The algebraic mark evaluates to the normalized abscissa at $1/N$ where $g_3 \ne 0$. |
| `restrict_modelGenerators` | The two model generators are represented by the holomorphic coordinate functions. |
| `restrict_modelG` | The restricted germ of (G) is represented by (g_2^3/g_3^2). |
| `restrict_modelX` | The restricted germ of the mark is the normalized abscissa at (1/N). |
| `splits_local` | The generic division polynomial splits over the prescribed meromorphic germ field at every parameter. |
| `map_mulX` | Base change commutes with the division polynomial ratio for multiplication. |
| `mulX_pointwise` | The ratio gives the normalized abscissa of the multiple whenever both points are affine at a generic parameter. |
| `periods_of_normX_eq` | Equal normalized affine abscissas have equal lattice classes up to sign. |
| `line_eq_of_coordinates_eq` | Normalized nonzero coordinates from different prime lines cannot agree. |
| `oneMultiple_val` | The representative of the first nonzero multiple is one. |
| `multipleUnit_coe` | The unit attached to a nonzero multiple has that multiple as its value modulo (p). |
| `multiplePerm_cast` | The permutation of nonzero multiples acts by multiplication modulo (p). |
| `multiply_period` | Multiplying two chosen representatives gives the permuted representative up to an original period. |
| `mulX_of_multiple` | The pointwise division ratio computes the permuted nonzero section. |
| `map_cluster` | Mapping an algebraic cluster maps the curve and its chosen generator. |
| `survives_map` | An embedding preserves the cluster predicate and the test for avoiding the marked order (p) point. |
| `map_veluPair` | A field embedding commutes with both algebraic Vélu coordinates. |
| `map_veluPair_kernelPerm` | An automorphism over the base sends both coordinates to those of the permuted surviving kernel. |
| `restrict_sectionAt` | Restricting a displayed torsion germ realizes the corresponding analytic section. |
| `eval_germ_polynomial` | Evaluating a polynomial of functions commutes with the germ quotient. |
| `restrict_local_poly_eval` | Evaluation of a natural polynomial of the local model is represented by evaluation on the complex normalized curve. |
| `local_roots` | The displayed meromorphic germs are exactly the local division roots. |
| `line_eq_of_sectionAt_eq` | Nonzero root germs from different lines cannot agree. |
| `restrict_mulX` | Local multiplication is represented by the pointwise division ratio. |
| `mulX_sectionAt` | Local multiplication on the root germs acts by the permutation of nonzero residues. |
| `analyticCluster_injective` | The weighted analytic multiset determines its line. |
| `cluster_sectionAt` | The algebraic cluster of any displayed root in a line is that line's analytic multiset. |
| `mark_multiple_section` | At a bad prime the local germ of the multiple (N/p) of the mark is the first horizontal section. |
| `branchLine_injective` | The allowed branches map injectively into the prime lines. |
| `exists_local_kernel_equiv` | An embedding of the splitting field identifies the weighted surviving clusters bijectively with the allowed local branches. |
| `veluPair_eq_familyPair` | The multiset Vélu formula on a finite family is the sum over its enumeration. |
| `familyPair_scale` | Rescaling the coefficients and the family by their weights preserves both coordinates. |
| `normalized_familyPair_eq_lattice` | Pointwise, the normalized algebraic formula is the short Vélu formula on the lattice cosets. |
| `restrict_analytic_pair` | The local pair calculated on the analytic cluster is represented by the two pointwise short sums. |
| `exists_embedding_of_pairedGerms` | Simultaneous germ matching of a pair gives an embedding of the model field taking its generators to that pair. |
| `primeTrace_of_kernel_profiles` | Local matches of all surviving kernels yield the exact prime trace after taking the sum. |
| `pairedGerms_of_restrict` | Equality of the two restricted germs along a continuous injective branch gives the required complex punctured germ comparison. |
| `continuous_injective_shiftDiv` | Each triangular parameter map is continuous and injective. |
| `continuous_injective_mulNat` | Multiplication of the parameter by (p>0) is continuous and injective. |
| `tendsto_punctured_branch` | A continuous injective branch map preserves convergence in the punctured neighborhoods. |
| `local_kernel_profiles` | For every parameter a single lift and a single bijection match both Vélu coordinates for every required branch. |
| `exists_primeTrace` | Every prime on any model satisfying the fixed hypotheses admits the exact trace morphism. |
| `bShStandardModel_proof` | The unchanged `R16Thm1.BShStandardModel`. |
| `heckeJ1DS_proof` | The unchanged `AfTateLam.HeckeJ1DS`. |
