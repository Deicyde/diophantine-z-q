# The conductor-one CM trace dictionary

**Scoped stop.** The exact `HKGZ.PoleCMTraceDictionary` and its extension
to every modular curve remain open. The algebraic part descends the
unaveraged Galois sum of a supplied point over the actual Hilbert class
field. Even granting a conductor-one reciprocity reading, the available
interfaces leave at least two distinct comparisons unproved: evaluation
of a CM point in the canonical modular curve model at the branch selected
by the existing Heegner form, and identification of the normalized
algebraic parametrization with `CST.phiAn`. Neither comparison gives the
other. This exceeds the one-GLUE budget; no replacement was folded.

The known citation gaps are the weak Weil premise in MPI/90-69 and the
apparent conjugate-eigenvector typo in the Shimura 1973 theorem used by the
existing newform route (details below). No new mathematical error was
found in the checked manuscript lines.

## What the trace proof supplies

For the actual `H = hilbertClassField K` and a given `y ∈ E(H)`,
[`existsUnique_point_of_sum_conjugates`](../../ZInQKernel/Contrib/OneProof/CMTraceDictionary/TraceDescent.lean) gives the unique `P ∈ E(K)` whose
base change is the sum of all `σy`. Each automorphism permutes the summands.
The coordinates of a fixed finite point descend by the fixed-field theorem;
the point at infinity descends separately. The base-change map is
injective. No division by the class number and no condition on the
elliptic curve's endomorphisms enter this proof. The scratch check reindexes
the sum through Tau Ceti's actual `hilbertClassArtinEquiv`; that does not
identify the individual complex summands with ideal-lattice translates.

For the pole case, the scratch check supplies the exact existing
`HKRefereed.IsHeegnerTrace` after the form, periods, rational scale, and
actual image with its `phiAn` equality are given. There is no new
Heegner-point predicate or input Prop. These are individual input data of
the existing predicate, before forming or descending the sum. The
generic proof of descent only takes an actual point and a Galois
extension; it asserts no CM property, existence of a modular map, or
existence of a point with a given complex image.

The [Lean substitution check](../../scratch/cm-trace-dictionary/Substitution.lean)
passed against the assembled pole modules. The five checked declarations
use only `propext`, `Classical.choice`, and `Quot.sound`; see the
[axiom output](../../scratch/cm-trace-dictionary/axioms-output.txt).

## Printed readings

These are separate reading slots. Locators marked **UNVERIFIED** have not
been checked against the primary page. No slot is rated LEAF or submitted
as a new Lean premise in this scoped stop. A reading desk check and two
independent reviews are needed before rating.

1. **Shimura reciprocity, SPECULATIVE; locator UNVERIFIED.** B. Gross,
   *Heegner points on X₀(N)*, in *Modular forms* (Durham 1983), published
   1984, §§1–3 (especially §3); alternatively G. Shimura,
   *Introduction to the Arithmetic Theory of Automorphic Functions*
   (1971), Chs. 5–6 (candidate Thm. 6.31, UNVERIFIED). For an oriented
   proper ideal pair at split level and maximal order, its canonical CM
   point is defined over the Hilbert class field; the ideal class of
   `b` acts by `[a] ↦ [a b⁻¹]` with arithmetic Artin. Check orientation,
   conductor one, inverse convention, even discriminants, all split
   primes including 2 when relevant, and the theorem on the canonical
   curve rather than only on `j`. Read the published action on a given
   CM class. It mentions no target elliptic curve, parametrization, or
   descended point. This is the field and action input at L2839–2844 and
   L2915–2917.
2. **`HeegnerTraceConjugationDraft`, SPECULATIVE; locator UNVERIFIED.**
   Reuse the separate `HKGZ` draft for sign −1. B. Gross and D. Zagier,
   *Heegner points and derivatives of L-series*, Invent. Math. 84
   (1986), 225–320, candidate Ch. V §2; alternatively Gross (1984),
   candidate §5. Check that conjugation of the oriented CM orbit is
   Fricke composed with a class group translation, and that the
   Fricke eigenvalue is `−w(E)` in the tree's convention for the
   functional equation. The translation reindexes the sum; the
   cusp constant then occurs `[H:K]` times. The expected assertion
   for both signs is that `σP − (−w(E)) • P` is torsion. Keep this as its
   own hypothesis for the general route. The existing odd-discriminant
   draft covers only `w(E) = −1`. The sign assertion assumes the trace
   already given and supplies no trace existence, rank or Sha. This
   checks the application at L1095–1097 using L2937–2946.
3. **Integrality of singular moduli, locator UNVERIFIED for this reading.**
   Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*,
   candidate Thm. II.6.1, already cited by the base's `CMjInteger`. Check
   the integral `j` formulation for the complex period lattice, including
   the passage from a noninteger lattice multiplier to CM. The printed
   integrality result has no CM point on a modular curve, map, or trace.
   L1012–1013 and L1765–1767 use its rational specialization. No new
   instance was supplied.

The prior `GrossZagierTraceDraft` remains a separate non-torsion input for
the pole submission. Its locator and scope remain as in the prior audit.
No Gross–Zagier proof is part of this work.

## Bridge audit

1. **`CanonicalCMEvaluationComparison`, open GLUE (L2839–2844,
   L2915–2917).** The existing `CST.IsHeegnerForm` and `CST.cmPoint`
   supply the analytic vocabulary. The function field
   `modularFunctionFieldQ` and its proved meromorphic q-expansion
   realization are useful infrastructure. Neither gives specialization
   at the place corresponding to this oriented ideal pair on the
   normalized curve. The older reciprocity interface for modular
   functions regular on the whole upper half-plane does not suffice for
   arbitrary pulled-back Weierstrass coordinates, which can have poles
   where the map lands at infinity. A specialization proof needs local
   rings or an equivalent construction, covering that case and the
   Artin action on the same branch. This comparison can be made without
   reference to `E` or its parametrization.
2. **`NormalizedParametrizationComparison`, open GLUE (L1779–1788).**
   The route through `modularToWeakWeil_of_printed` in `AllPrints.lean` supplies
   an analytic weak Weil parametrization, conditionally on the listed
   inputs. Its period proof gives a period relation and does not export
   equality of the algebraic and analytic evaluations. Match the
   normalized Abel–Jacobi map followed by the optimal quotient and the
   rational isogeny to `E` with the existing Eichler integral and its
   rational scale; identify the canonical conductor with the Lean
   least cusp-form level. The existing `HKGZ.newformLevel_eq_of_isNewformOf`
   compares that least level with the level of a Lean newform.
   `RC.PrintsAnalytic.modularNewform_of_printed` is already the
   conditional supplier for that newform from the existing readings.
   A rational isogeny commutes with conjugation and addition, so the
   image of an unaveraged sum is the sum of the images; a finite
   kernel preserves non-torsion. The isogeny and the normalized
   equality need to be attached to the same map, even if one uses
   this functoriality. Matching the differential alone is insufficient:
   translating the map by a rational point `Q` would change the trace
   by `[H:K] • Q`. This comparison can be made without choosing `K`.
3. **`PolePeriodNoCM`, outstanding pole compatibility (L1012–1013,
   L1765–1767).** `RC.PrintsArith.curve_j` calculates `35152/9`;
   `curve_hasNoCM` uses `CMjInteger` for the algebraic endomorphism
   predicate over the algebraic closure of ℚ. The `IsNonCMLattice` required by the exact pole
   predicate is expressed using complex lattice multipliers. The
   weak Weil witness does not contain it. The lattice integrality
   reading could support a proof, but no such specialization has
   been applied here.
4. **CCL reuse boundary (L2915–2936).** `GenuineHeegnerAnchor`
   in `H20Anchor.lean` takes as data both field rationality over `D.H d` and the
   equality with `phiAn`. `CCLThm2_15Applied` asks for an anchored
   witness satisfying the norm relations; the relations alone admit
   the zero datum. Also `D.H 1` is not definitionally the
   actual Hilbert class field. The existing field dictionary can
   transport a genuinely anchored datum with its field
   identifications. It does not produce the datum or the image
   equality from the bare norm relations. Those norm relations
   are at moving conductors; they are not needed for unweighted
   descent from `H₁` to `K`.
5. **Unaveraged trace descent and reindexing, proved.** The two results
   above use the actual field, its Galois automorphisms and the actual
   Artin equivalence. Conjugation over `ℚ` and any cusp correction
   remain in the separate sign hypothesis.

Items 1 and 2 are names for open work, not added assumptions. Combining
them into an input that produces a point `y` with the desired image
equation would hide the point-construction part of the dictionary.

## Consumer delta

- **`hk-gz`: actual delta 0.** The scratch substitution packages the
  original trace predicate from an image and calls the existing
  `hkConsumed_of_grossZagier` with its exact dictionary and separate
  sign premise. It leaves `PoleCMTraceDictionary` open and
  `LiCarayolNewformOfModular` untouched. A completed dictionary would
  remove the former GLUE from that conditional route, leaving the
  existing newform input and the previously listed source readings.
  Replacing the dictionary now by the two unproved comparisons would
  add at least one GLUE slot to that route.
- **`Prints.kolyvagin`: actual delta 0.** The general trace operation
  itself works on any `E`. The existing witness predicate cannot be
  the unrestricted dictionary, because it imposes `IsNonCMLattice`.
  The image comparison needs to work also for CM targets; the height
  and arithmetic readings must accept that same image and the sign
  must cover both root numbers. It is enough for the audited
  auxiliary-field route to use odd discriminants by splitting at 2;
  the proposed general dictionary may exclude −3 and −4 and must
  address the other even discriminants if claiming the full requested
  scope. After the dictionary, the source readings and the rank-zero
  derivative specialization, the remaining arithmetic work is the
  full Sha comparison and restriction, plus exact rational rank
  descent in the two eigenspaces. This is not a claim of a provider
  for either forward-rank case.
- **General-form consumers.** `forwardRank_zero_of_prints` applies to
  arbitrary elliptic curves. `core34'`, `core34`, `fixedWitness_proof`,
  `genusIndex_eq_top_of_not_simpleZero` and `exact_twist_of_genusPoint`
  take twists of general base models. `selmerCorankOneOverK_of`,
  `CalibrationModelP.nonempty_modelR`, `forward_corankZero`,
  `selmerCorankOneOverKSigned_of_forward` and the two even-upper
  adapters take twists of pole-family curves; the target twist is
  not restricted to the pole congruence family. Signed calibration
  uses both forward cases and both Sha outputs. See the
  [consumer audit](../../scratch/kolyvagin-prints/consumers.md) and the
  [substitution dry run](../../scratch/cm-trace-dictionary/substitution.md).

## Known issues

- **Build constraint missed on the initial dependency invocation.** Lake
  resolved the original toolchain's Lean binary and bypassed the worker
  lock. The invocation was stopped once this was found; its aggregate
  worker times confirm overlap. The subsequent build and checks use a
  toolchain path with the locking wrapper as `bin/lean`, with the load
  and memory checks and `LEAN_NUM_THREADS=4`.

- The forward theorem cited at L1093 assumes a weak Weil
  parametrization at the conductor; the previous audit found the
  cited MPI/90-69 source unrefereed. `IsModular` in the existing
  consequence form does not encode that premise. The manuscript
  spells out the intended passage for the pole curve at L1779–1788.
- The existing coefficient-field reading records an apparent typo
  in the theorem statement of Shimura 1973: the eigenvector on the
  right of the conjugate relation should be the conjugate form.
  The base cites the proof on p. 527 for that reading; this task
  did not reread the primary page.
- Normalizing the map at infinity does not make the Fricke
  translation vanish at the other cusp. The manuscript includes
  this correction. The exact sign and its source locator still
  need the reading desk.

## Manuscript check

Each line refers to `diophantine_zq.tex`.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1006–1013, L1761–1767 | Pole domain and nonintegral (j). | **OK** — the same model and (j) value occur in Lean; passage to its period lattice is still open. |
| L1086–1093 | Forward rank zero and one for a general elliptic curve, with modularity. | **unverified** — the cited forward theorem's weak Weil premise needs the comparison above to replace it via an auxiliary field. |
| L1094–1096 | Choose the auxiliary field and use the conductor-one Heegner point in the height and arithmetic theorems. | **unverified** — no CM image supplier, and exact journal scope remains to be read. |
| L1096–1097 | Descend rank and Sha from the quadratic extension. | **unverified** — still needs the separate conjugation input and the full quadratic Sha comparison. |
| L1111–1115 | Use forward rank for the pole point arguments. | **OK** — the existing pole assembly needs only an infinite-order rational point. |
| L1779–1784 | Newform at the conductor and elliptic quotient. | **unverified** — the conditional newform extraction exists; formal level versus canonical conductor must be checked. |
| L1785–1788 | Apply the rational isogeny and normalize the Abel–Jacobi map at infinity. | **unverified** — normalized algebraic evaluation versus `phiAn` remains open. |
| L2836–2844 | Fix the normalized map and a split CM field, and use its conductor-one ring class field. | **OK** — the trace proof uses the actual Hilbert class field of the base field. |
| L2915–2922 | Choose the oriented CM point and evaluate the normalized map over the ring class field. | **unverified** — the conductor-one specialization at the canonical CM branch remains open. |
| L2923–2936 | Compare moving-conductor norms. | **OK** — this is a different sum and is not an input to the trace proof. |
| L2937–2946, L8282–8285 | Keep the cuspidal translation in the Atkin–Lehner formula. | **OK** — the manuscript retains it; the trace sign reading and compatibility with the target map remain unverified. |
| L4345–4347 | Use the specified conductor-one point after the height formula. | **unverified** — trace descent alone supplies no height conclusion. |
| L8213–8220, L8261–8266 | Use the unaveraged ideal-class sum; at the degenerate address the genus character is trivial. | **gap filled** — Lean reindexes and descends the unweighted conductor-one sum after the image is supplied. The general weighted case is outside this proof. |
| L8249–8256 | Split the auxiliary discriminants at 2 and the old primes. | **OK** — the available BFH statement supplies the required clauses; the rank-zero derivative specialization remains to be checked. |
| L11155–11186 | Identify the cited quotient construction, cusp torsion, height formula, auxiliary-field theorem and CCL relation. | **OK** — these citations are present; they do not verify the proposed reciprocity and sign locators. |
