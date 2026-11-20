# Independent even inventory and fixed-place carrier

**Result, with a scoped stop at the Galois inputs.** For one tested set
`U`, the actual moving and unary cuspidal lists give an independent
`BlocksPerU.Inventory`, with one source for each normalized newform and
one column for each distinct old degree. Each block keeps its intrinsic
level and character. From a single original place above two, the
construction gives a separate receiving completion and stable integral
lattice for this set. The carrier’s coefficient and seed identities
discharge the coordinate premise of `budgetRealization_of_joined_scoped`.
The joint rules and seed follow given the intrinsic good-prime
attachments and the added-prime local cuspidal comparison listed
below. The even budget row is still conditional on those inputs.

**Inherited manuscript error:** the simplified expansion in tex
8162–8167 omits a base factor; the Lean proofs use the exact expansion
in tex 8168–8182. No new manuscript error was found.
## Independent inventory

VERIFIED: for one tested set, take the finite image of all occurrences of
`(normalized newform, old degree)` in the actual moving and unary lists.
The source index is the finite image that forgets the degree. Equal
occurrences therefore share both their Fourier column and their Galois
source. The lift to `N = movingLevel P U` records the divisibility at the
original level before lifting the character. The independent presentation
retains every distinct old degree; it does not extract a basis of a larger
space by dropping arbitrary columns.

STANDARD, locator UNVERIFIED: W.-C. Li, *Newforms and functional equations*,
*Math. Ann.* 212 (1975), Theorem 5 and its corollary. The new printed-form
input is `OldNewIndependenceWeightTwo`, linear independence of all
genuine normalized cuspidal newform dilations `f(dτ)` at `N` with
`d * level(f) ∣ N`. For each nebentypus it is the old/new direct sum (the trivial-character case is due to Atkin–Lehner,
*Math. Ann.* 185 (1970)); different nebentypus spaces are independent diamond eigenspaces. The
reading desk should check the locator and general-character formulation.
Correction after the page check: Li's Theorem 5 (p. 298) is strong
multiplicity one, and Li uses old/new independence (pp. 302, 309) without
proving it. The leaf is renamed `OldNewIndependenceWeightTwo` and cites
Diamond–Shurman, GTM 228, Theorem 5.8.3 (locator UNVERIFIED), with
Atkin–Lehner, Math. Ann. 185 (1970), Theorem 5, p. 151 for trivial character.
The Lean argument transports this one input through the injective
Fourier map and restricts it to the finite image.

VERIFIED: the extension field contains the genuine newform coefficient
fields and the values of all lifted block characters, including an
empty block's character. Finitely many roots of unity suffice for the
latter. One prime of this compositum lies over the receiving copy of
the original fixed prime. The individual block span uses exactly the
columns whose source level times degree divides the block level and
whose pulled-back character is the block character. The actual blocks
are already proved cuspidal; no general Eisenstein splitting is used.

## Fixed source and place

The source comparison uses a map from `C₀.K₀` to the fixed embedded number
field, together with its two commuting embedding equations. In the
fixed-place producer `EvenPlace.sourceAtPlace` the map is the identity:
`K₀ = F`, `eC = F.subtype`, and `eK = FinitePlace.embedding V.v`.
That producer and the retained phase order are standing inputs, chosen
once. Every receiving field for a row uses its own place over `v`.

## Global and local obligations

Tex 9652–9654 and 9762–9769: the intrinsic good attachment is
`BlocksPerU.SourceAttachment (Y.sourceLevel s) (chooseFrob frobeniusExists)
(Y.source s)` for each source of the placed inventory. This only asserts
matrix continuity, ideal-theoretic unramifiedness and the specified
arithmetic Frobenius trace and determinant. It supplies no lattice,
joined coordinates, or budget realization. The tree already has
`CarayolRefold.CarayolThmAFrob` with both Frobenius values; the narrower
`CarayolPrinted.CarayolThmA` has only the trace. The coefficient fields are equal by
`NormalizedCuspSource.attachment_field`. Remaining glue: restrict
the chosen prime to the source's coefficient field, extend the completed
representation to the row's field, and compare the valuation-subring
and ideal descriptions of Frobenius and inertia. Owner: modular Galois.

The prime-comparison statement needed in this transport is: for a
rational prime `q` and a maximal `Q : Ideal Zbar` containing `q`,
give a valuation subring `v` of `Qbar` above `q` such that
`IsArithFrobAt ℤ σ Q` gives `PkgI4.IsArithFrob σ v q` and each
`σ ∈ Q.inertia GalQ` lifts to an element of `v.inertiaSubgroup ℚ`
with underlying automorphism `σ`. The natural ring to compare is
the localization of the algebraic integers at `Q`; its valuation
property can be tested in finite number fields. This route is unchecked.

Tex 9754–9760, 9773–9861: the added-prime data is the existing
`O12Local.CuspidalData` on the same source representations and
dilation coordinates, together with support of the seed and
`WhittakerComparison` for their operator. For the ramified factors,
the existing computations take the actual primitive central
character, the Casselman and Carayol comparison data, and the
induced model. On the prime-to-`p` coordinates the old operator
is allowed to mix degeneracies. Producing a full local operator on the
ambient oldspace would require accounting for any further degeneracy
columns it produces; the required comparison is at coefficient one.
This request does not contain
the reduced (O.12) equation or the separately realized row.
Owner: local modular models.

## Construction and handoff

- `DistinctCuspColumns`: `coeff_zero`, `coeff_mem_field`, and
  `char_mem_field` identify the source coefficients and character in
  the genuine coefficient field. `source_dvd` and `coeff_form` give
  the level and coefficients of the dilation. `cuspDilation_coeff_independent` carries the print
  through the injective Fourier map. `liftColumn_level`, `liftColumn_char`,
  `liftColumn_coeff`, `liftColumn_field`, and `mem_distinctCuspColumns`
  identify each occurrence in the merged finite list.
- `ExactInventory`: `charAt_apply`, `eigen_a`, and `eigen_char` compare
  the placed coefficients and characters with the genuine ones.
  `cuspSource_dvd`, `cuspSource_exists`, `cuspSourceCoeff`, and
  `cuspSourceChar` pass to the finite source image. `cuspInventory_coeff`
  and `cuspInventory_char` identify the inventory's columns and diamonds.
- `AttachmentCoefficients.attachment_field` removes the zero constant
  coefficient from the field of the Galois print.
- `PlacedInventory`: `exists_placedCuspLists` constructs the finite
  compositum and receiving prime. `in_image`, `blockChar_complex`, and
  `block_span` transport the intrinsic spans on the actual columns.
- `PlacedSeed`: `evenBlockLevel_dvd`, `movingLevel_ne`, and
  `movingLevel_test_coprime` give the level and good-test domain.
  `timesTheta_map_ringHom`, `unaryCoeff_map_ringHom`, `TL_map_scaled`, and
  `blockSeriesAt_map` transport the two block series.
  `exists_actual_placed_lists` instantiates the lists and their place.
  `fieldMap_complex`, `fieldMap_source`, and `ringMap_agrees` give the
  three embedding comparisons. `exists_placed_block_vectors`,
  `placed_evenVector_eval`, `phase_complex`, `rawSource_complex`,
  `vectors_spec`, `seed_support`, `seed_complex`, and `seed_integral`
  identify the support and all Fourier coordinates of the divided seed.
- `PlacedDiamond`: `even_blockChar_sign` computes the quadratic signs;
  `placed_diamond_eval` proves that every diamond translate stays
  integral and has integral corrections in the undivided unary blocks.
  `blockChar_on_representative` and `quadValue` evaluate the lifted
  characters on diamond representatives. `phase_ring` and
  `block_scalars` lift the phase and its sign differences;
  `scaled_shell` and `unary_integral` put the raw shell and undivided
  unary coefficients in the ring, and `diamond_seed_vector` applies
  their correction to the coordinates.
- `PlacedFreshCoefficients.fixedH_two_fresh` proves the required
  divisibility in the original ring. `OneSeedLattice.oneSeed_same`,
  `oneSeed_other`, `oneLatSeed_val`, and `oneSeed_integral` describe the
  single active seed. `oneCoeff_hecke`, `oneLattice_stable`, and
  `oneSeed_trace_inertia` use the actual Hecke and diamond span, good
  Frobenius limits, and formwise inertia. `oneSeed_twoTrace` applies
  density to two fresh primes avoiding the index and one another,
  using `dense_pair_avoid`.
- `OneSeedModel`: `oneSeedModel_column`, `oneSeedModel_seed`, and
  `oneSeedModel_hecke` are the positive coefficient, seed, and good Hecke
  equations of the formwise constructor. Its off-row seeds are zero;
  they do not represent other tested sets.
- `PlacedTrace`: `integral_diamonds`, `unary_inertia`,
  `lattice_seed_coeff`, and `fresh_coeff_mem` specialize the integral
  orbit to the actual row. `PlacedDeterminant.determinantData` uses the
  exact diamond correction, the residues computed by `scalar_residue`
  and `odd_residue`, and the unary square support.
- `PlacedModel`: `model` and `extension` specialize the carrier and the
  normalized place. `model_base`, `model_source`, `model_maximal`,
  `model_hecke`, and `model_coordinates` fill the corresponding
  premises of the scoped producer directly. `fixedRing_continuousSMul`,
  `two_mem_extended`, and `maximal_closed` provide continuity of
  scalar multiplication, the residue prime above two, and closedness
  of the maximal ideal of the extension.
- `CuspidalLocal.cuspidalStage` uses the supplied cuspidal comparison
  and the vacuous Eisenstein shift `emptySector_shift`.
  `localAt_of_cuspidal` supplies the old local
  binder. `budgetRealization_of_placed` and
  `rules_and_seed_of_placed_joint` feed the separate rows to the merged
  joint quotient consumer.

`PlacedCuspLists` records a number field, a prime over the fixed prime,
and containment of the actual coefficients and characters; there are no
spanning or Galois fields in the structure. The theorem
`exists_placedCuspLists` supplies it. `sourceAttachments` specializes
an existing structure to the actual finite source index (tex
9652–9654, 9762–9797). `CuspidalLocalAt` requests only the local
cuspidal data at each added prime, on the given carrier (tex 9754–9861).
`PlacedGaloisInput` combines the two compatible requests, allowing a
receiving field large enough for the local scalars. The column and seed
match, coefficient ring, lattice, determinant identities, and budget
are all constructed after these inputs. In particular no hypothesis
asserts the budget or a new deletion identity.

## Known issues

- **Inherited manuscript error (tex 8162–8167).** The simplified
  expansion omits a base factor; the proofs use the exact expansion in
  tex 8168–8182. See the previous inventory report.
- Diamond translates alone need not form a Hecke stable span. The
  construction takes the integral span of both good Hecke and diamond
  translates (tex 9660–9668).
- The Li theorem and corollary locator is **UNVERIFIED**. No new manuscript
  error was found in the checked steps.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited missing base factor in simplified expansion. |
| 8168–8182 | OK | Exact expansion used by the moving and unary laws. |
| 9636–9645 | OK | Fixed-ring divisions precede reduction; the receiving valuation restricts to the fixed one. |
| 9646–9654 | gap filled | Construct the placed finite column space for one set; the actual blocks are cuspidal. Good Galois attachment remains a separate input. |
| 9655–9659 | gap filled | Exact sign difference times the scaled shell gives the integral diamond correction. |
| 9660–9668 | gap filled | Good Hecke recurrence, finite coordinate injection, closed lattice, and both stable operators. |
| 9696–9710 | OK | Phase reduces to one; source and fixed place stay the same as the set changes. |
| 9712–9739 | gap filled | Actual determinant correction on the chosen lattice, with unary square support; use the existing orbit proof. |
| 9741–9750 | gap filled | Two-fresh annihilation from the fixed ring; formwise inertia for the quadratic quotient. |
| 9754–9764 | gap filled | Intrinsic level and character spans and old degrees are retained; inertia on unary coordinates omitting the prime follows from their source level. |
| 9765–9797 | unverified | The good polynomial is in the existing Carayol print; its attachment in the ideal-theoretic model requires the bridge above. |
| 9799–9861 | unverified | Existing local computations are reusable once the actual cuspidal comparison is attached. |
| 9866–9918 | OK | Use the already formalized local and symbolic reading with the scoped data. |
| 9919–9932 | OK | The merged joint quotient reads omission using the two separate row models. |

Count delta: one printed form added (Li 1975); no new axiom or
registered provider; no existing declaration changed. The new files
and their handoff compile with Lean 4.35.0. The reproducible axiom check
in `scratch/rc-even-inventory2/Audit.lean` covers 129 declarations,
including private lemmas; its output uses only `propext`,
`Classical.choice`, and `Quot.sound`.
