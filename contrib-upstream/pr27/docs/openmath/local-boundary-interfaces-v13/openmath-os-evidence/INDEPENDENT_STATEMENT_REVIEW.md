# Independent statement and application review — PR #2

## Scope, notation, and verdict

This review covers exactly PR #2, head
`3e01aa877cd7434fdc759fe7b6a9271de6deff2e`. Its base is
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`; merge integration is separately
identified as `b6223977015d6f25baf613d0c88a5c83050f9c84`. The mathematical
sources are byte-identical to research commit
`33483f751e6dcd3f91fb303969838aca33ad0458`.

The four formal modules, all 41 explicit roots and all 16 printed definitions
were read and compared with the application table and the stated source
consumer passages. The independently generated native statement/axiom export
is used for corroborating the elaborated text, rather than replacing source
inspection. No defective local deduction was found within the declared scope.
The application boundary is genuine: the actual arithmetic cup/trace
integration, continuous Galois/Selmer realization, inverse existence and
integrality regimes, determinant-basis normalizations and all-limit
localizations remain outside this PR.

This is a bounded mathematical source review. It is not independent human
acceptance of the manuscript, external-kernel verification, or a claim that
all source applications have been constructed in Lean.

## Root-by-root semantic check

The count and order match `TARGETS.json` exactly: **19 + 8 + 7 + 7 = 41**.
There are two homotopy-valued definitions among these roots, so "41 theorems"
should not be interpreted as 41 proposition-valued tautologies.

### `ConjugateLocalTransport` (19 roots)

For these results let ρ be the actual twisted action αT restricted to the
named normal subgroup, d the specified transporter satisfying φ = dτ with
T(φ)=T(τ), and u=α(d)⁻¹. The source hypothesis `LocalData` does **not** assert
a scalar transport formula or normalized coordinate evaluation as an axiom.

| # | Root | What the elaborated statement actually proves, and guard |
| ---: | --- | --- |
| 1 | `crossed_conjugation` | Full cocycle conjugation with all p(a) and action terms. Only trivial action at the evaluated local element may erase them. |
| 2 | `crossed_pow_of_trivial` | If the element acts trivially, its nth power has the expected cocycle value, including n=0. Division by a prime to one is not used. |
| 3 | `LocalData.tate_transporter` | The representation equality plus τ²=1 gives T(d)=1. No algebraic inversion of a finite-parameter ideal occurs. |
| 4 | `LocalData.twist_transporter` | Consequently the twisted action of d really is the scalar action α(d)I. This is not asserted as a separate normalization hypothesis. |
| 5 | `LocalData.twist_transporter_inv` | The inverse action is uI, where u=α(d)⁻¹ is the specified integral unit. It applies to a range-specific integral-stage claim, not to an inflation of scalar units into a different ring. |
| 6 | `LocalData.tate_finite` | The Tate action at the generator φ² is trivial, using the given actions, not assumed borrowing from unramified cohomology anywhere else. |
| 7 | `LocalData.twist_finite` | The corresponding twisted finite action is trivial; it combines T(finite)=1 with α(finite)=1. |
| 8 | `LocalData.twist_inertia` | The twisted inertia action is similarly trivial. Closedness/homology of a cocycle is not being asserted. |
| 9 | `LocalData.rawConjugate_isCrossed` | Raw pullback is a crossed cocycle for the **pulled-back** representation ρ∘conjτ, not necessarily for the original ρ. This preserves the carrier distinction. |
| 10 | `LocalData.conjugation_finite` | Raw conjugation of φ² is expressed as d-conjugation of φ², with direction and group membership preserved. |
| 11 | `LocalData.conjugation_inertia` | Raw tame conjugation is expressed using the specified ℓth power, without yet identifying ℓ with −1. |
| 12 | `LocalData.rawConjugate_finite` | Finite coordinate after raw conjugation is u times the original, using the trivial finite action and d's scalar, not a primitive class substitution. |
| 13 | `LocalData.rawConjugate_inertia` | Tame coordinate is u times `(ℓ:R)` times the original. The finite-group and characteristic-specific congruence is still explicit. |
| 14 | `LocalData.coordinates_rawConjugate` | Pair of coordinate evaluations has exactly `(u f, u ℓ s)`. This general nonvanishing or nonquadratic character case is kept separate from the tame minus-one restriction. |
| 15 | `LocalData.coordinates_rawConjugate_of_neg_one` | The same pair specializes to `(u f, -u s)` **only if `(ℓ:R) = −1`**. No natural prime is accidentally set to −1 in characteristic zero. |
| 16 | `LocalData.twist_conjugation_finite` | The finite element also acts trivially in the conjugate coefficient representation, needed for well-defined cohomology evaluation there. |
| 17 | `LocalData.twist_conjugation_inertia` | The corresponding inertia action is trivial in that same conjugate representation, not imported by identifying it with the original. |
| 18 | `LocalData.coordinates_add_coboundary` | Adding an actual coboundary does not change either coordinate, because evaluation happens at trivially acting elements. |
| 19 | `LocalData.conjugate_coordinates_add_coboundary` | That invariance remains valid on the distinct conjugate carrier. This is not a finite-to-continuous or nonflat base-change theorem. |

### Degree-one group cohomology (8 roots)

The carrier here is Mathlib's actual quotient of inhomogeneous one-cocycles
by their actual coboundaries. `H1π` and `H1_induction_on` are the relevant
operations, not a new abstract class whose equations were engineered to
produce the desired conclusion.

| # | Root | Checked meaning and guard |
| ---: | --- | --- |
| 20 | `h1_projection_surjective` | Every genuine H¹ class has an inhomogeneous cocycle representative. It constructs no continuous Galois class. |
| 21 | `cocycleEvaluation_kills_kernel` | At an element x with ρ(x)=1, evaluation kills the actual coboundaries. Dropping this condition is an invalid shortcut; the C8-style negative control requires it. |
| 22 | `h1Evaluation_projection` | Evaluation descends to actual H¹ with the correct formula on a cocycle representative. The instance at a nonzero-action element would be different. |
| 23 | `cocyclePullback_kills_kernel` | Pullback sends an original coboundary to a coboundary of the composed representation, so it respects the kernel of genuine H¹ projection. |
| 24 | `h1Pullback_projection` | The genuine H¹ pullback has the explicit formula on representatives. Its original and pulled-back carrier types remain different. |
| 25 | `LocalData.h1Coordinates_projection` | Finite/singular coordinates on a represented H¹ class reduce to the raw values at the source's two specially chosen elements. |
| 26 | `LocalData.conjugateH1Coordinates_projection` | The raw conjugate coordinate positions have the analogous well-defined property on the conjugate H¹ carrier. |
| 27 | `LocalData.h1_local_transport` | Pullback of an arbitrary genuine finite-group H¹ class has precisely the shared-unit coordinates already proved on cocycles, including the explicit tame minus-one when `(ell:R)=-1`. Base change to a limiting Selmer class is still an application obligation. |

### Local cup and trace (7 roots)

The two Leibniz identities are displayed hypotheses of `LocalCupData`; there
is no hidden boundary–duality or normalization premise. A source cycle must
have `localCondition = localGlobal + d0(q)`, and its boundary direction must
be closed. A chain trace must kill the target differential.

| # | Root | Checked meaning and guard |
| ---: | --- | --- |
| 28 | `closed_cup_differential` | Closed l gives `cup11 l (d0 q) = -dt (cup10 l q)`. The minus sign is retained; it is the source of the correction in the next lemma. |
| 29 | `pure_boundary_correction` | Substitution of the actual cone-cycle equation gives an exact difference between local-condition cup and global-local cup. This is not simply assumed to vanish without the local correction. |
| 30 | `traced_pure_boundary` | A trace that kills coboundaries removes that correction and yields equality of the two traced cup values. A common trace is still external source input. |
| 31 | `traced_left_boundary` | A boundary in the left cup argument is zero after trace because the other argument is closed, using the other displayed Leibniz law. |
| 32 | `traced_right_boundary` | A boundary in the right cup argument is zero after trace because the left argument is closed, using the same closed-cup correction. |
| 33 | `traced_change_left` | Consequently a representative change by a coboundary does not change the left cup value; its other argument is supplied closed. |
| 34 | `traced_change_right` | The counterpart for a right coboundary also holds, with the closedness condition on the left argument. Both boundary placements matter. |

### Cone comparison and orthogonal comparison (7 roots)

| # | Root | Checked meaning and guard |
| ---: | --- | --- |
| 35 | `fibreComparison_commutes` | The degreewise map `(g,u,q) ↦ (g,a u,q+h u)` commutes with the H22 differential when a is a chain map and `inc−inc'a=dh+hd`. This is not a full complex/duality-isomorphism existence theorem. |
| 36 | `fibreComparison_global` | The first component of that map is literally unchanged. It proves only the projection part, not arbitrary local-condition equality. |
| 37 | `fibreComparison_sign_change` | Changing q_H to q_N=−q_H corrects the third component to q_N−h u. The two different cone conventions are not silently identified. |
| 38 | `inverse_preserves_global_homotopy` | A supplied right inverse k with `k≫j ~ id` and common projection `j≫q=p` gives `k≫p ~ q`. This is an actual homotopy-valued construction and counts as a root. |
| 39 | `inverse_preserves_global_homology` | That homotopy yields equality of true homology maps, not just equality at the level of arbitrary cochain representatives. |
| 40 | `inverse_preserves_local_homotopy` | Postcomposition by a genuine chain map preserves the induced homotopy. This is the second homotopy-valued root, not an inference from a localization map being an isomorphism. |
| 41 | `inverse_preserves_local_homology` | The localized homology maps are therefore equal. There must exist and be identified the source right homotopy inverse at the relevant coefficient/localization; no integral inverse is inferred from a mere generic one. |

## The 16 tested definitions and their meaning-carrying hypotheses

| Definition(s) | Review of meaning, quantification and carrier |
| --- | --- |
| `twist`, `conjugation`, `IsCrossed` | The twist is the actual scalar action composed with the Tate action, restricted to H, and conjugation is `h ↦ τhτ⁻¹` in the normal subgroup. The cocycle law is the additive crossed rule `p(gh)=p(g)+ρ(g)p(h)`. |
| `LocalData`, `transportUnit`, `coordinates`, `rawConjugate` | The fields contain representation/group relations, not a desired normalized coordinate formula. `transportUnit = α(d)⁻¹` is integral. `coordinates`: `(p F,p I)` are actual evaluation positions. Raw conjugation is pullback by τ with a distinct coefficient carrier. |
| `cocycleEvaluation`, `h1Evaluation` | Evaluation at x is kernel-respecting only when the action at x is trivial, in which case it lifts honestly to actual H¹ using `liftOfSurjective`. |
| `cocyclePullback`, `h1Pullback` | These act on inhomogeneous cocycles and their H¹ quotient respectively, with representation composed with the group homomorphism rather than ignored. No identification with the original representation is inserted. |
| `LocalData.h1Coordinates`, `conjugateH1Coordinates` | These package the finite/inertia evaluations on the corresponding genuine H¹ carriers. They do not assume global continuity or an arbitrary map on all cohomology after coefficient localization. |
| `LocalCupData` | It stores only the two local differentials and cups with two explicit Leibniz rules. It is not a complete DGA or a complete Selmer complex; the target application must still supply the actual cup maps and common chain trace. |
| `fibreD`, `fibreComparison` | Their raw third coordinates implement H22's `loc−inc−dq`, respectively the corrected `q+h u` map with identity on the global component. The sign convention used by the cup correction must be translated rather than silently changed. |

## Application correspondence and remaining obligations

- **Local cocycle/conjugation:** arithmetic occurrence requires the intended twisted Tate system, odd good derivative place, H12, character triviality, compatible finite/tame generators, and a common quotient retaining the actual two classes and actions. The tame relation must be exact in that quotient. These are not synthesized by the formal LocalData constructors.
- **Mathlib H¹ later use:** actual continuous cocycles and coordinate maps must be identified compatibly at each finite precision. Retaining limiting tuples, inverse pairs and contractions is separate. Cohomology need not commute with arbitrary nonflat coefficient base change, and the explicit limitation on ℓ=−1 must not be applied directly in characteristic zero.
- **Boundary cup:** the actual localized cup and its closed orthogonal partner, the pure connecting representative, compact-support cup and a common global/local trace square remain to be instantiated. The abbreviated interface correctness is not the full boundary–duality theorem.
- **Orthogonal comparison:** the degreewise map requires real chain maps/homotopies in each degree. The deeper homology result needs the source comparison/right-inverse data under the permitted integral/localized regime. Generic inverses, or a nilpotent finite-stage parameter-inverse, are not enough.
- **Downstream application:** no actual common-strict matrix or stored row is created by these declarations. Original determinant bases and `HasCoordinate` interpretations are not guessed from equal dimensions. Full determinant preservation and outer-limit rank reduction are not claimed by the packet.

## Independent source-diff and scope findings

- The PR is additive: `git diff base..head` shows no semantic edits to the frozen
  common-strict packet, prior historical verdicts or manuscript data.
- The two support-only additions after the core review snapshot are publication
  preparation/review evidence, not changes to the mathematical modules.
- There is no latent axiom of global Poitou–Tate adjunction in the selected import
  graph. The input hypotheses are the actual lower-level maps/homotopies. This
  limited interface does not secretly pass off the target normalizer equality as
  its hypothesis.
- `LocalCupData` need not enforce a full complex differential equation for all
  of the displayed results. Similarly, the pure degreewise fibre samples in the
  finite tests need not claim all assembled chain complexes. These are correctly
  bounded rather than semantics bugs, but they cannot be used as evidence of a
  fully constructed Selmer model.
- The step from finite-stage values to limits must retain inverses and class maps;
  abstract existence of an H¹-style identity is not a substitute for that work.

## Adverse-control interpretation

The control program calculates genuine nonzero exact cup corrections,
degreewise cone maps, homotopy identities and genuine cocycle/coboundary
relations. It explicitly rejects nonclosed boundaries, wrong signs, wrong
coefficient carriers, a non-chain trace, a missing common projection after a
side-changing inverse, duplicate J, independent primitive-row normalization,
and optimization that would disable assertions. Its evidence concerns the
documented failure modes, not exhaustive occurrence in Galois cohomology or
unimodular integral pairings. A separate `.git` ownership/cache setup defect
and job timeout encountered in this review are operational logs, not proof
findings.

## Conclusion

The selected four proofs are valid bounded conditional interfaces under source
inspection and the independently regenerated native axiom/statement audit.
Their correct claims are local cup/cocycle corrections, shared-unit transport
through actual finite H¹, and global/local homology preservation through a
supplied right inverse. No hidden target determinant-normalization conclusion
has been silently introduced.

The important acceptance boundary remains that successful execution does not
instantiate the global arithmetic cup/trace normalization or its determinant
bases. The separate outer parity-checker replay is an additional evidence
layer and must be read independently of this semantic acceptance.
