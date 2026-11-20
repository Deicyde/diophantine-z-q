# The forward rank field in Theorem 5.3

**Scoped stop.** The auxiliary-field route exceeds the GLUE budget for
`Prints.kolyvagin`. Even if Theorem 5.3 supplies its existing newform
extraction, the route still needs a CM trace dictionary for the actual
consumer curves and a full Sha comparison and descent at the chosen
quadratic field. The field currently counts as one GLUE under the
unrefereed-source rule. No field or consumer is discharged, and the
parked pole hypothesis is unchanged. No new Lean declaration was made.

The source audit found 16 direct calls in ten theorems, plus the two
explicit even-upper adapters. Some need only a bound on Mordell–Weil
rank; others pass full Sha finiteness to the existing Kummer interfaces.
In particular, signed calibration takes both rank/Sha pairs, and the
general rank-zero adapter quantifies over every elliptic curve over ℚ.
The [sizing log](../../scratch/kolyvagin-prints/log.md) records the exact
field and the [consumer list](../../scratch/kolyvagin-prints/consumers.md)
records their curves and projections. The PR #163 variants are absent
from the pinned base.

## Known issues

- **VERIFIED (prior source audit and current Lean definitions).**
  Theorem 1 of MPI/90-69 is in an unrefereed preprint and assumes a weak
  Weil parametrization at the conductor. The bare `IsModular` premise of
  `KolyvaginThm1Printed` only supplies a coefficient-matching cusp form
  at some positive level. The old field is a consequence form, and the
  analytic weak-Weil variant still has a dictionary to the algebraic
  parametrization. See `docs/research/audit-pole-hypotheses.md`, §6.
  This is a citation and interface gap, not a counterexample to the
  forward-rank lemma.
- **VERIFIED (existing source reading).** The retained Shimura
  coefficient-field route records an apparent typo in Shimura 1973,
  Theorem 1: the eigenvector on the right of the displayed conjugate
  eigenform relation should be the conjugate form. The base cites the
  proof on p. 527 for that reading. This task did not reread the page.
- **UNVERIFIED (source scope).** The 1988 Kolyvagin article advertises a
  subclass. The reading desk must verify its defining conditions before
  using it at arbitrary modular curves. For Gross's exposition, also
  distinguish an opening statement of the full theorem from any
  prime-by-prime proof with stronger hypotheses. Finiteness at selected
  odd primes does not imply the full Sha result or even the required
  finiteness at two. No new mathematical error in the checked manuscript
  steps was established.

## The proposed readings

These are page-reading targets, with **UNVERIFIED** locators. None is
rated LEAF. The reading desk should check the printed statements on the
page and submit them to the two-lens skeptic pass before introducing
formal leaves. The arithmetic payload is over actual elliptic-curve
points and Galois cohomology, with no abstract rank or Sha objects.

| Candidate print | What to check |
| --- | --- |
| Bump–Friedberg–Hoffstein, *Nonvanishing theorems for L-functions of modular forms and their derivatives*, Invent. Math. 102 (1990), 543–618; introductory theorem, clauses (i) and (ii), candidate pp. 543–544 (**UNVERIFIED** in this audit). Reuse `RC.PrintsAnalytic.BFHTheorem`. | Weight two and trivial character, the actual twist, negative fundamental discriminant in each relevant sign/clause pair, all primes of the finite set splitting (including 2), and respectively a simple zero or a nonzero value. Existence alone is used. This supplies the auxiliary field at L1094–1095, independently of any arithmetic rank conclusion. |
| Gross–Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986), 225–320; elliptic-curve height formula for the trivial class character, exact page **UNVERIFIED**. Reuse the proposed consequence `HKGZ.GrossZagierTraceDraft` in its checked scope. | The trace is the conductor-one Galois sum of the actual CM image. Check split level (including 2 if it divides the level), extra units, the specific modular map or optimal quotient, and that switching to the curve's uncompleted continuation preserves nonvanishing of the derivative. Check whether the height formula applies in the required CM cases. The consequence is non-torsion of that trace over the selected field, no rational rank or Sha. This is L1095. |
| Kolyvagin, *Euler systems*, in *The Grothendieck Festschrift*, vol. II, Progr. Math. 87 (1990), arithmetic theorem for a non-torsion Heegner trace; exact locator **UNVERIFIED**. Alternative reading of the same slot: Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and Arithmetic*, LMS Lecture Note Ser. 153 (1991), opening arithmetic theorem; exact page and numbering **UNVERIFIED**. | Read the standing assumptions on the parametrization, conductor-one point, split field, field discriminant, and any conditions at 2 or other primes. Check that the theorem yields rank one (or finite index of the subgroup generated by the trace) and finiteness of the **whole** `Sha(E/K)`. If Gross only proves a selected-prime statement, locate the proof of the full assertion in Kolyvagin. The hypothesis is a genuine non-torsion Heegner trace, and the output concerns the quadratic field only. This is L1095–1096. |
| Gross–Zagier (1986) or Gross (1991), Atkin–Lehner comparison under complex conjugation; exact locator **UNVERIFIED**. The base `HKGZ.HeegnerTraceConjugationDraft` covers sign −1 only. | Check both signs in one conjugation statement: the trace should have eigenvalue `−w(E)` modulo torsion. Verify the cusp correction, normalization of the rational map, and passage from one Heegner point to the Hilbert class field trace. This locates the one nonzero line in the descent at L1096–1097. There is no rank or Sha claim in this input. |

The rank-zero citation to audit separately is Kolyvagin, *Finiteness of
E(Q) and Sha(E,Q) for a subclass of Weil curves*, Izv. Akad. Nauk SSSR
52 (1988), theorem and page **UNVERIFIED**. The proposed route uses the
same arithmetic input over the auxiliary field for both ranks, so the
1988 paper is an alternative reading, not a fifth premise. In
particular, a statement beginning with `L(E,1) ≠ 0` on a subclass
cannot supply the unrestricted rank-zero clause without identifying
and establishing the subclass conditions. The manuscript's separate
Kato option at L1104–1108 is outside this auxiliary-field route. The
existing `KatoCor14_3` in `RC/PrintsArith/Kato.lean` already records
its changes of premise and its Kummer and Bloch–Kato comparisons; it
cannot be counted as a new leaf that bypasses those comparisons.

## Bridges and count

1. **Newform extraction, GLUE shared by the lane** (L1092, L1779–1784).
   Use `RC.PrintsAnalytic.modularNewform_of_printed`, as
   `RCLeaves.modularNewform` already does with `Prints.bcdt`.
   The two existing open readings are
   `Carayol1986RationalNewformEulerFactors` and
   `Faltings1983EulerFactorRigidityQ`; the Shimura and Li print inputs
   are also already in `RCLeaves`. Alternatively the same bridge can
   be costed as the single grouped premise `LiCarayolNewformOfModular`.
   It supplies a coefficient-matching newform and no points, ranks or
   Selmer data.
2. **Auxiliary field and derivative, GLUE partly proved on the base**
   (L1094–1095). For analytic rank one, the functional-equation sign
   is −1, and `HKGZ.exists_auxiliary_of_bfh` uses BFH(ii)
   to choose a negative discriminant `D` with nonzero twist value.
   `HKGZ.exists_baseChange_simple_derivative` gives the derivative of
   the untwisted base change. For analytic rank zero, the sign is
   +1; BFH(i) instead gives `D < 0` and a simple zero of the twist.
   The same construction with splitting at 2 and all level primes,
   and the same proven factorization, would give
   `L′(E/K,1) = L(E,1)L′(E^D,1) ≠ 0`. The rank-zero specialization
   was checked on paper against the source types and was not compiled.
   No Gross–Zagier argument is needed for the derivative calculation.
3. **CM trace and algebraic comparison, open GLUE** (L1094–1096,
   L1781–1788). Reuse `HKGZ.PoleCMTraceDictionary` at its pole-family
   instances. Outside those instances it supplies no witness, even
   when the curve in a generic consumer happens to be non-CM. To
   cover the whole field, the existing trace representation's
   `IsNonCMLattice` condition must also be removed with the
   correspondence checked, or handled by a separate CM argument.
   The required interface produces the point over the Hilbert class
   field on the actual curve with its actual descended trace, and
   compares the algebraic parametrization and conductor with the
   existing analytic definitions. It must not assume non-torsion or
   give any arithmetic conclusion.
4. **Mordell–Weil descent, GLUE partly proved on the base** (L1096,
   L4022–4025). With `K = ℚ(√D)`, the + eigenspace of
   `E(K) ⊗ ℚ` comes from `E(ℚ)` and the − eigenspace
   comes from `E^D(ℚ)`. The twist isomorphism changes sign
   under the nonidentity automorphism; sum and difference give the
   projections after dividing by two. A non-torsion trace in rank
   one spans the whole space. In the analytic-rank-one case the
   trace is in the + eigenspace, giving ranks `(1,0)`. In the
   analytic-rank-zero case it is in the − eigenspace, giving `(0,1)`.
   `HKGZ.exists_rational_of_conjugate_sub_torsion` already proves
   positive rational rank on the + side. Exact ranks and the
   twist-side transport were not assembled in Lean here. Rank zero
   gives a torsion group; finiteness of that point group also uses
   finite rational torsion, or finite index over the Heegner field
   if the arithmetic source supplies that stronger conclusion.
5. **Full Sha comparison and restriction, open GLUE** (L1096–1097).
   `RC53Assist/CentralSelmer/QuadraticDescent.lean` gives
   `res_mem_shaK`, `cor_mem_sha`, the twist comparison on its
   `shaK` in the completed-square model, and the underlying
   index-two cohomology identities. Identify the selected field's
   full local kernel in the arithmetic theorem with this restriction
   target. Restriction on each rational Sha then has finite image
   and kernel contained in the respective `Sha[2]`, by
   corestriction after restriction. Finish using finiteness at level
   two (the finite Kummer sequence and finite 2-Selmer), including the
   model change for the twisted restriction if needed. A kernel
   killed by two is not automatically finite. In particular the
   comparison of the two eigenspaces of the Mordell–Weil
   tensor cannot replace this step or give an integral decomposition
   of full Sha. This bridge uses finiteness over `K`, with no
   assumption on analytic rank or on the source curve's rational rank.

**Count delta.** Actual: no changes, no new LEAF ratings. Hypothetical:
remove one GLUE field and add at least three open GLUE obligations for
a standalone supplier (grouped newform extraction, CM trace, full Sha
descent), a net increase of at least two. In the lane, charge newform
extraction to the existing `RCLeaves` fields: the two remaining open
obligations still give a net increase of at least one. This is a lower
bound, granting the rank and elementary analytic transports as
provable glue. The four print slots above include BFH already stated in
the tree; there are at most three further candidates to activate for
the lane, and no source rating changes without the reading desk.
No new interface was declared. Verification of this stop is a
source audit; there are no new Lean axioms to print.

## Manuscript check

All lines are in `diophantine_zq.tex`. The verdict is for the indicated
step, not for the whole argument it appears in.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1086–1092 | Define the two forward cases and invoke BCDT. | **OK** — the modularity predicate is available from the retained BCDT statement. |
| L1093–1096, L11161–11167 | Obtain the auxiliary field, nonzero trace height and finiteness over the field. | **unverified** — the cited preprint is open GLUE; the replacement journal and book readings still need their source and dictionary checks. |
| L1096–1097 | Control the restriction kernel for Sha. | **unverified** — the index-two computation explains the exponent bound, but this audit does not close the full Sha comparison and finite-kernel proof in Lean. |
| L1098–1104 | Use Kummer to turn the rank and Sha results into a Selmer corank. | **OK** — the current consumers use the rank-one Kummer interface and the proved rank-zero corank theorem, or the caller's rank-zero Kummer hypothesis. |
| L1104–1108 | Separate rank-zero argument from Kato's Corollary 14.3. | **unverified** — no primary-page review or modular-quotient and Selmer comparison was done here. |
| L1779–1788 | Pass to a newform and the rational algebraic modular parametrization. | **unverified** — the coefficient route is retained; it does not construct the map and CM image used by the two prints. |
| L1984–1992, L8249–8256 | Use BFH for splitting and the complementary nonzero twist value or derivative. | **OK** — the base's BFH statement contains the two distinct sign and discriminant clauses; the rank-zero auxiliary uses the simple-zero clause at sign +1. |
| L2386–2387, L10140–10142 | Use rank-zero forward corank in the rough companion estimate. | **OK** — this is the audited `forwardRank_zero_of_prints` route. |
| L2461–2467, L8261–8272 | Rule out the unwanted genus component by rank zero. | **OK** — the corresponding Lean calls use only the rank projection to get torsion. |
| L2616–2626, L5264–5267, L10276–10281 | Use the companion's corank zero in the rational sum of coranks. | **OK** — this consumes the rank-zero forward input; no integral direct-sum identity is required. |
| L4020–4027, L4050–4059 | Use rank one, finite Sha and the sum/difference maps at calibration. | **unverified** — the consumers read both forward cases; the proposed two-sign rank and full Sha descent are not closed. |
| L5734–5736 | Use untwisted quadratic factorization with a nonzero complementary value. | **OK** — the base proves the factorization on the convergence half-plane and its use via the product rule at the simple zero. |
| L7624–7627, L7780–7781 | Supply even rank-zero corank and finiteness hypotheses from a nonzero value. | **OK** — the existing Lean forward adapters read those two projections. |
