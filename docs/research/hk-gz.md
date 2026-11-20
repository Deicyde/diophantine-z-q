# Gross–Zagier route to the consumed pole input

**Scoped stop: keep `hK` on the open list.** The Lean-checked conditional substitution reaches
`HKConsumed` without MPI/90-69. It uses three printed candidates (two new
statements and the existing BFH statement) and still needs two independently open
GLUE inputs: newform extraction from the BCDT cusp form and realization of the
conductor-one Heegner trace in the algebraic/analytic dictionary. Two GLUE rows
exceed the one they would replace. No headline, ledger or existing statement changed.

The input is precisely the stage-one `HKRefereed.HKConsumed`: for positive
squarefree `ℓ ≡ 11 (mod 12)` with `(PoleRC.SelM ℓ).ncard = 8`, a modular
`E_ℓ` of analytic rank one must have an infinite-order point in `E_ℓ(ℚ)`.
The count is used in the existing Kummer argument; it does not enter the
Gross–Zagier argument. Neither rank exactly one nor finiteness of Sha is an
output of this reduction.

## Printed candidates

1. **`GrossZagierTraceDraft` — SPECULATIVE; locator UNVERIFIED.** B. Gross and
   D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
   (1986), 225–320. Look for the elliptic-curve consequence of the height formula
   for the trivial ideal-class character. For an imaginary quadratic field
   of odd discriminant splitting every conductor prime, a nonzero derivative of the untwisted
   `L(E/K,s)` forces the conductor-one trace to have infinite order. Check the
   exact page, split hypothesis at all conductor primes including 2, discriminant
   restrictions, choice of optimal quotient versus a parametrization over ℚ,
   and the trace and height conventions. In particular, check the transfer
   under the rational isogeny and that the printed (L)-function/derivative
   agrees in nonvanishing with the uncompleted continuation in Lean. The draft
   uses the existing `HKRefereed.IsHeegnerTrace` predicate, including the
   actual Hilbert-class-field sum; this predicate is not itself the paper's
   algebraic dictionary.
2. **`BFHTwistNonvanishingDraft` — VERIFIED (base Lean statement);
   locator UNVERIFIED for this reading.** D. Bump, S. Friedberg and J. Hoffstein,
   *Nonvanishing theorems for L-functions of modular forms and their
   derivatives*, Invent. Math. 102 (1990), 543–618, §0, candidate locator
   pp. 543–544, clause (ii). Reuse `BFHTheorem` from
   `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/BFH.lean` on the pinned base;
   the existing file records a prior reading of the journal scan. The adapter
   takes its second output, for a level-`M` newform of weight two and trivial
   character. Check on the page that the split set can include any finite set
   containing all level primes, that the sign condition is `εD > 0`, that
   the discriminant is fundamental, and that the nonzero central value is
   for the Kronecker twist. No infinitude or prime-count bound is used.
3. **`HeegnerTraceConjugationDraft` — SPECULATIVE; locator UNVERIFIED.**
   Gross–Zagier (1986), or B. Gross, *Kolyvagin's work on modular elliptic
   curves*, LMS Lecture Note Ser. 153 (1991), in the discussion of
   conjugation of conductor-one Heegner points or their trace. Check
   the actual Atkin–Lehner formula, the sign convention (expected trace
   eigenvalue `−w(E)` modulo torsion), and the cusp correction under the
   parametrization. Check that summing over the class group gives this
   assertion for the odd-discriminant trace, including any torsion translation and the
   passage from the optimal quotient to the chosen target curve. The draft
   asks only for the `w(E) = −1` case. No exact identity before killing
   torsion or arithmetic rank over `K` is assumed.

All three are pending the reading desk and two independent checks; none is rated
LEAF here. The older general positive-rank composite is not used.

## Bridges and count

- **Open GLUE: `LiCarayolNewformOfModular`.** The headline's printed BCDT condition
  (2) gives the coefficient-matching cusp form via `bcdtThmA_of_printed`.
  The existing `modularNewform_of_bcdt_liCarayol` turns it into the
  level-`M` newform that BFH and the Artin factorization use. The base has a
  conditional supplier for this input with Shimura, Li, and the Carayol and
  Faltings readings. These premises are not headline inputs. Expanding
  that supplier would expose its own two candidate prints and two GLUE readings;
  reusing a conditional theorem does not discharge its premises.
- **Open GLUE: `PoleCMTraceDictionary`.** Supply the CM image over the Hilbert
  class field and its descended Galois sum for the selected `K`, with
  the analytic map and level read in the conventions of the print. The existing
  BCDT-to-weak-Weil route is conditional and reaches a complex analytic model;
  it does not identify it with an algebraic `X₀(N) → E` at the conductor,
  or supply the algebraic CM point. The draft requires a witness to the
  existing trace predicate. The source comparison includes the equality of
  the formal newform level and the printed conductor (in its algebraic
  sense). The Lean proof identifies the least coefficient-matching cusp-form
  level of the trace dictionary with the level of the BFH newform.
- **GLUE, proved:** BFH's curve adapter and Hasse convergence already exist.
  The new argument gets sign `−1` from the functional equation and the simple
  zero. BFH splits at 2 as well as at the primes of the newform level. The selected
  negative discriminant is odd (indeed `1 mod 8`), so there are no extra units.
  The proof constructs the quadratic field, identifies its discriminant and
  supplies splitting in its actual ring of integers.
- **GLUE, proved:** specialize the existing Artin factorization to the trivial
  character and conductor one, identify the resulting Euler product with
  Mathlib's `L(E/K,s)`, and use the product rule at 1. In particular the
  derivative is `L'(E,1) L(E^D,1)` since `L(E,1) = 0`.
- **GLUE, proved:** multiply the trace by a positive integer killing
  `σP − P`. The resulting point is fixed by the nonidentity quadratic
  automorphism and descends by the existing point-descent theorem.
  The multiple and the descended point still have infinite order.

**Count delta.** The actual headline delta is **0**. A hypothetical substitution
removes one `hK` GLUE row and adds two named GLUE rows (**net +1 GLUE**
even after favorable readings) plus three pending printed slots (**net +4
open slots**). BFH is reused from the tree, but is not an independent premise
of this headline. There are no newly rated LEAF rows. The scratch check keeps
the stage-one height supplier as a parameter, to be instantiated by
`HDec.HSyn.sixContactMin_of_open91`; the BCDT adapter, pole proof and
final assembly are the actual ones. All five modules and both scratch checks
passed with `lake env lean`. The nine new module theorems and the substitution
theorem use only `propext`, `Classical.choice`, and `Quot.sound`; see
`scratch/hk-gz/axioms-output.txt` and `scratch/hk-gz/Substitution-output.txt`.

## Known issues

- The manuscript's cited forward-rank source is the unrefereed MPI/90-69,
  with a weak Weil parametrization premise. This work supplies a candidate
  route around that preprint only for the consumed point-existence fragment.
- Non-torsion over an imaginary quadratic field alone says nothing about
  whether its trace contributes to the rank over ℚ or to the quadratic
  twist. The sign of the trace under conjugation is a separate premise.
- The analytic trace dictionary does not establish the algebraic comparison
  or prove existence of a CM image over the class field. These are GLUE.
  No mathematical error was found in the checked pole steps.
- **Build constraint missed:** the initial dependency build used Lake's
  default worker scheduling because the co-located toolchain took precedence
  over the serialization wrapper. The final build and checks explicitly
  selected the wrapper and ran one Lean process at a time.

## Manuscript check

Lines are in `diophantine_zq.tex`.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1001–1011 | Pole completeness uses the restricted converse to produce analytic rank one. | **OK** — the restricted converse remains a headline input. |
| L1012–1013 | Nonintegral rational `j` supplies the non-CM setting for the curve family. | **OK** — the trace dictionary still has to realize the required lattice. |
| L1033–1035, L1065–1069 | Both parameters are in the family and give eight explicit Selmer classes. | **OK** — this is the domain of the stage-one consumer. |
| L1072–1084 | Dimension three gives corank one using the Cassels–Tate pairing. | **OK** — the same retained pairing input is used. |
| L1086–1097 | The forward theorem is invoked with modularity and an auxiliary Heegner construction. | **unverified** — the manuscript cites the preprint here; the proposed replacement supplies only the rank lower bound and its journal locators remain open. |
| L1111–1115 | Apply the forward theorem twice and realize the prescribed classes by points. | **gap filled** — stage one uses Kummer counting once an infinite-order point is supplied, without finiteness of Sha. |
| L1116–1121 | Coordinate changes finish pole completeness. | **OK** — the existing pole assembly is reused. |
| L1779–1788 | Produce the level-`N` newform and the algebraic map via the elliptic quotient of `J₀(N)`. | **unverified** — both the newform input and the algebraic-to-analytic trace dictionary remain GLUE in this substitution. |
| L5734–5736 | Use the untwisted quadratic factorization and nonzero complementary value. | **OK** — the same identity is used in the other direction, to compute the derivative over `K`. |
| L8249–8254 | Given root number `−1`, use BFH(ii) for a negative discriminant with split old primes and nonzero central value. | **OK** — the existing BFH statement gives this; the present root number comes from analytic rank one. |
| L11161–11174 | Identify the Gross–Zagier, Kolyvagin and BFH bibliography. | **OK** — these are the manuscript's references; the exact Gross–Zagier pages for the two draft statements are unverified. |
