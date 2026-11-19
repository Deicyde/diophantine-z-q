# Prime traces on the fixed standard model

**Scoped stop: the generic marked quotient family over the model's function
field remains open.** Lean proves the simultaneous complex lattice
comparison for both coordinates and the implication from a compatible
finite Galois family to the exact `BShStandard.IsPrimeTrace`. Neither
`R16Thm1.BShStandardModel` nor `AfTateLam.HeckeJ1DS` is discharged.
No new leaf or fold.

The bridge between Shimura's standard model and the kernel's model is in
neither the manuscript nor its citations. The recorded reading in
[r16-thm1b.md](r16-thm1b.md) gives rational Hecke operators on Shimura's
own model. It does not identify those operators on an arbitrary model
satisfying the kernel's specific generation and point predicates.

## ON THE SPOT (provenance (c)): the lattice calculation

Index the larger lattice by pairs `(i,l)`, with `l` in the old lattice
and image `l-rᵢ`. Reindex the absolutely convergent Weierstrass series
before splitting the outer sum. Subtracting the translate at the origin
is essential: the two separate unregularized inverse square sums do
not justify the calculation. Reindexing the inverse fourth and sixth
power sums and computing the local Taylor coefficients gives the short
Vélu corrections to the two Weierstrass coefficients.

With short coefficients `a,b`, a kernel point of x-coordinate `t`
contributes `T = 3t²+a`, `W = 5t³+3at+2b`. Pair the marked translates
by the sign permutation of the nonzero cosets and use the addition
formula. The contribution to the x-coordinate of a surviving mark
`x` is `T/(x-t) + 2(t³+at+b)/(x-t)²` per nonzero coset. The
formula uses all nonzero cosets, so the coefficient and coordinate
sums count both members of an opposite pair. For an order-two point
there is only one such coset and `t³+at+b=0`. This gives the
order-two coefficient correction and removes the second term from
the marked-coordinate shift. Compute `j` and Weber from the same
three resulting scalars.

The triangular lattices preserve the order of the mark. The horizontal
lattice has periods `1/p, τ`. There the multiple `k/N` is a period
exactly when `N ∣ pk`: for prime `p`, this lattice retains the full
order exactly when `p ∤ N`. Scaling by `p` turns the periods into
`1,pτ` and sends `1/N` to `p/N`. The predecessor's diamond identity
then gives both coordinates at `g(pτ)` for the specified lower-right
entry of `g`.

To see that these are the prime kernels over the complex lattice, write
`pw = a+bτ` for a nonzero torsion class. Modulo `p`, if `b=0` it lies in
the horizontal lattice only; otherwise the unique triangular index is
`i=a/b`. This uses the uniqueness of integral period coordinates.
The normalized division-polynomial theorem identifies the pointwise
roots with the x-coordinates of all nonzero classes killed by the given
integer.

## ON THE SPOT (provenance (c)): the trace from generic branches

Let `K = ℚ(X)`. Given a finite Galois extension `L/K` and a family of
field embeddings `bᵢ : K → L` permuted by `Gal(L/K)`, pull the generic
point back along each embedding. Compose with Abel–Jacobi and take the
product in the group of `L`-points. This is the sum in geometric
notation. Base change commutes with that product, so even with repeated
entries an index permutation fixes the product. The predecessor's
Galois descent and proper extension theorems give the desired morphism
from `X`.

For specialization, there is a field of punctured meromorphic germs at
each parameter and a valuation ring given by its elements with a
finite limit. A comparison on the two generators determines the
comparison on the whole function field. If the corresponding pulled
back germ has a finite value at a stalk element, the stalk evaluation
lifts the branch through the finite-germ valuation of `L`. Along the
generic inclusion one obtains the generic branch; along evaluation
one obtains the specified `AtTau` point. Apply separatedness of the
Jacobian to the product and the morphism, then specialize and split the
finite index type. The local comparison may use a different
permutation at each parameter; no consistent labelling is required.

## Smallest remaining input

Construct the embeddings `bᵢ : K → L`, with the one horizontal branch
included only at good primes, and the following simultaneous
comparison. For each `τ`, find an embedding from `L` to the
meromorphic germ field extending the source embedding of `K`, and
a permutation of the index type such that the images of
`(bᵢ j_X, bᵢ t_X)` are the pairs of holomorphic coordinate germs
pulled back by the required branches. The same permutation must
apply to both coordinates, including multiplicities. Over `K`
the family must be permuted by the Galois group. This is the
coordinate form of the branch hypothesis to
`exists_primeTrace_of_coordinate_germs`. It would give `IsPrimeTrace`, and the existing
`bShStandardModel_of_primeTraces` then gives both target statements.

A direct route is to use the predecessor's normalized curve with
`G = 27 j_X/(j_X−1728)` and marked x-coordinate
`46656 t_X/(j_X−1728)`. Work in the splitting field of the prime
division polynomial, using x-coordinates of nonzero torsion modulo
sign. Multiplication on these coordinates is by the division
polynomial ratios. This identifies which roots lie in the same
cyclic subgroup and which subgroup is excluded by the mark. To apply
the complex formulas in the splitting field still requires several
linked lemmas. First show that the pointwise exhaustion gives a
splitting polynomial over the meromorphic germ field at every upper
half-plane point. Mathlib's splitting-field lift then gives the local
embeddings. Next transport the partition into cyclic kernels and the
test for the kernel that meets the mark through these embeddings, and
form the algebraic Vélu pair for each surviving kernel. Keep
division-polynomial root multiplicities separate from the indexing by
cyclic kernels: the latter counts one entry per kernel, even if two
coordinate pairs coincide. Finally compare the resulting pairs with
the pulled-back coordinate germs. The proved
`exists_ringHom_of_pair_relations` turns the matched pairs into
embeddings once their relations agree. This is a substantial field and
torsion comparison (several hundred lines of Lean), rather than another
numerical identity of invariants.

The vendored modular-polynomial root and product theorems give
j-coordinates. The odd-prime Vélu point homomorphism supplies the
algebraic point map over an algebraically closed field. They do not
give a branchwise Weber comparison in the germ field or construct
the required model embeddings. The direct coset calculation is used
for the analytic marked coordinate and includes the separate
order-two weights.

## Lean statements

Names in this table are in the `BShTraces` namespace. Private helpers
are listed by their source names.

| Theorem | Statement |
| --- | --- |
| `weierstrassP_cosets` | For a finite coset enumeration of a superlattice, its Weierstrass function at `z` is the sum of `℘(z+rᵢ)−℘(rᵢ)` over the old lattice's cosets. |
| `G_cosets` | For `n>2`, the superlattice's Eisenstein sum is the sum of the old lattice's translated inverse `n`th-power sums. |
| `representative_mem` | Every representative belongs to the superlattice. |
| `lattice_le` | With a zero representative, the smaller lattice is contained in the larger one. |
| `representative_notMem` | With a zero representative, no other representative belongs to the smaller lattice. |
| `exists_neg_perm` | Negation permutes the nonzero cosets, modulo the smaller lattice. |
| `invPow₄` | Off the lattice, the shifted fourth-power sum `S₄(w)` satisfies `6S₄(w)=6℘(w)²−g₂/2`. |
| `invPow₆` | Off the lattice, `120S₆(w)=120℘(w)³−18g₂℘(w)−12g₃`. |
| `short_coefficients_of_cosets` | The superlattice has short coefficients `a−5∑T` and `b−7∑W`. |
| `short_pair_weights` | On a short model, the vendored opposite-pair weights are `2T, 2W, 4(t³+at+b)`. |
| `short_two_weights` | For a point `(t,0)` on a short model, the order-two corrections are `−5T,−7W` and the marked shift is `T/(x−t)`. |
| `weierstrassP_add_formula` | For two affine uniformized points of unequal x-coordinate whose sum is affine, the Weierstrass addition formula equals the short-curve slope formula. |
| `short_shift_of_opposites` | Off the poles, the two opposite marked translates, each with `℘(w)` subtracted, sum to twice the short shift. |
| `short_mark_of_cosets` | Where the translates and denominators are defined, the marked x-coordinate changes by the sum of the short shifts over the nonzero cosets. |
| `short_coordinates_scale` | Rescaling the two coefficients and marked coordinate by `u²,u³,u`, for `u≠0`, preserves the rational coordinate pair. |
| `short_weights_scale` | Under the same scaling the three short summands scale by `u²,u³,u`. |
| `short_coordinates_of_cosets` | Given the nonvanishing and coset hypotheses, the single short Vélu calculation gives the pair `(jL M,weber M z)`. |
| `x_ne_of_sub_add_notMem` | If neither argument nor their sum or difference is a period, the two x-coordinates differ. |
| `short_coordinates_of_surviving_mark` | If the mark survives the lattice quotient and the target is in the generic Weber normalization, the short Vélu pair equals the target lattice pair. |
| `rem_lt` | For positive `p`, the nonnegative integer remainder of division by `p` is less than `p`. |
| `coordinateEquiv_apply` | Transport of a coordinate equivalence to the period lattices acts by the target period expansion. |
| `horizontal_periods` | The horizontal lattice has periods `1/p,τ`. |
| `horizontal_diamond` | The horizontal lattice with mark `1/N` has the pair of the diamond translate of `pτ`. |
| `mem_pp_of_im_zero_iff` | The real elements of the lattice of `τ` are exactly the integers. |
| `triangular_mark_order` | The multiple `k/N` is a period on a triangular branch iff `N ∣ k`. |
| `horizontal_mark_order` | The multiple `k/N` is a period on the horizontal branch iff `N ∣ pk`. |
| `period_coords_inj` | The integral coordinates of a period are unique. |
| `prime_torsion_lattice_unique` | Each nonzero class killed by a prime belongs to exactly one horizontal or triangular superlattice. |
| `normalized_torsion_roots` | For a generic lattice, the normalized division polynomial vanishes exactly at normalized x-coordinates of nonzero classes killed by the given integer. |
| `meromorphic_isField` | The subring of punctured germs admitting meromorphic representatives is a field. |
| `fieldGerm_coordinates` | The two generic model generators map to the germs of `Jf` and `Wf N`. |
| `generic_j_ne` | The generic generator `jX` is neither `0` nor `1728`. |
| `exists_ringHom_of_pair_relations` | Matching the integral polynomial relations of a generating pair with those of a pair in a second field gives an embedding taking one pair to the other. |
| `comp_prod_points` | Base change of a finite product of Jacobian points is the product of the base changes. |
| `exists_extension_of_permuted_branches` | A Galois permutation of the generic branches makes their Abel–Jacobi sum the restriction of a morphism from `X`. |
| `specialize_sum_of_branches` | Equality of the morphism and the sum over the fraction field of a valuation ring implies equality after evaluation. |
| `exists_branch_lift_of_stalk_values` | If the field embedding gives the finite values of a point's stalk, the generic branch lifts through the finite-value valuation and specializes to that point. |
| `atTau_eval` | A function field element with a finite germ value at an `AtTau` point is represented by a stalk element with that value. |
| `atTau_stalk_value` | Every stalk element at an `AtTau` point has the corresponding finite germ value. |
| `triangular_coordinates` | The triangular Vélu pair is the pair at `(τ+i)/p`, in the generic Weber normalization. |
| `horizontal_coordinates` | At a good prime the horizontal Vélu pair is the pair at the specified `g(pτ)`, in the generic Weber normalization. |
| `ringHom_eq_of_generators` | Ring maps out of the function field that agree on its two generators agree everywhere. |
| `transfer_of_generator_germs` | Agreement on the two generator germs after reparametrization transports all finite germ values. |
| `exists_primeTrace_of_branch_germs` | A finite Galois family permuted by Galois and admitting all the required local finite-value comparisons gives the exact `IsPrimeTrace`. |
| `exists_primeTrace_of_coordinate_germs` | For that same conclusion it suffices to compare the two named coordinate germs, simultaneously, after reparametrization at each branch. |

The offline `lake build` of `+ZInQKernel.Contrib.OneProof.BShTraces`
succeeded for the root module and all its helpers. Each of the 45
`#print axioms` checks lists only `propext`, `Classical.choice` and
`Quot.sound`. There is no `#discharges` output for the open row.

## Known issues

- The prior page reading records a typo in Shimura's sentence on
  coefficient conjugates before clause (iv) (p. 526 as recorded):
  the eigenvalue should multiply the conjugate newform. That sentence
  is outside the quotient construction used here.
- The Euler identity in the print is a total product. Extracting the
  constituent at the specified coefficient embedding requires a
  separate representation argument.
- Diamond–Shurman §§6.3 and 7.9 and Shimura 1971 §7.2 are background
  locators, UNVERIFIED. No theorem from those locators is taken as a
  leaf.
- At the exceptional parameters the pointwise Weber formula switches
  normalization. The `AtTau` comparison uses the punctured germ of
  the generic branch; agreement at an individual exceptional point
  is not imposed.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L768, passage to the primitive newform | unverified | The twisting and primitive normalization are outside the prime-trace proof. |
| L768–770, Fricke stability | unverified | The earlier audit checked the Fricke proviso conditional on the coefficient conjugates being newforms. This run does not recheck Li's page or use that proviso. |
| L770–771, rational quotient and Hecke action | OK | The recorded reading establishes this on Shimura's own standard model. |
| L770–771, analytic part of the prime-operator comparison | gap filled | The simultaneous lattice calculation gives the marked coordinate as well as the invariant, and explains the extra diamond in the good-prime branch. |
| L770–771, comparison of prime operators with the fixed Lean model | unverified | The manuscript and its citations do not give the model bridge. The lattice calculation and the conditional specialization are separate glue; the generic marked correspondence remains open. |
| L771, Euler-factor identity | OK | The recorded reading confirms the total identity under the Fricke proviso. |
| L771–772, Tate constituent at the chosen embedding | unverified | The total Euler identity alone does not identify the fixed constituent. This run does not attempt the representation argument. |
| L773, identification of its cohomological dual | unverified | This run does not check that representation dictionary. |
| L11053–11057 | OK | The bibliography identifies Shimura's article, the cited theorem, and the DOI. |
