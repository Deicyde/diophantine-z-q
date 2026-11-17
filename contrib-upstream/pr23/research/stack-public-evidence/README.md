# Public evidence for the conditional-quartic stack (#8 to #20)

This packet is additive. It changes no file outside this directory. It commits,
for each of the 12 selected tables of PRs #8, #9, #11, #12, #13, #16, #17,
#18, #19 and #20:

- the complete decimal table;
- the balanced integer quadratic rows whose sum of squares is the table, both
  as the original JSON and as an easy-to-parse plain-text file;
- the IRs and maps that lead to those rows, and the existing transformation
  certificates and check reports.

It also contains a standalone checker, exact-rewrite certificates for #13 and
#18, and an errata note. It answers gaps 1 and 2 of Carlos Toledo's non-author
review of #8 to #16: the residual rows were unpublished, and seven of his eight
tables existed only as fork CI artifacts that expire on 2027-02-06. It also
records his wording note on the precision-51 recurrence ([ERRATA.md](ERRATA.md)).

**What this packet is not.** It is not a review, an acceptance record, an
application contract or a manuscript change. It authorizes nothing under
`docs/research-review/PROTOCOL.md` or `docs/audit-history/PROTOCOL.md`. The
packet author is the stack's author, Cameron Freer, working with an AI agent,
so none of its checks is non-author evidence. A passing check settles a finite
algebraic statement. It does not settle any arithmetic argument, any inherited
input or the conditional theorem.

## Sources

Every file came from one of these sources:

- the frozen #20 commit `75e7630341e0722aca7bca414e10b6ff003ba498`, which
  contains all ten packets, and the public PR heads listed below. Each head
  is an ancestor of the next. From one head to the next, files under
  `research/` are only added, so every earlier packet is byte-identical at
  `75e76303`;
- the public review archive at `452c8620a47752d58b42ca44d8432a907f89fae5`,
  `research/independent-local-reviews/2026-11-09`, used read-only as a source
  of published hashes;
- read-only local build directories of reproduction runs at those heads.
  `INDEX.json` (`origins`) records the build path of every file. A file from
  a build is public evidence only to the extent that its hash is bound, as
  described next.

Before any file was copied, its SHA-256 was compared with every hash the
frozen packets or the archive publish for that build path. For #8, its byte
count was also compared. No compared file differed, so none was excluded.
A file counts as **bound** in either of two cases:

- its hash is published in one of those sources (`pathBinding` or `publishedIn` in `INDEX.json`);
- its hash is stated inside another bound file in this packet (`statedIn`).
  For example, a diagonal certificate whose hash is published names its
  source and target IRs by hash.

Of the 216 copied files, 132 are bound and 84 are not. Each unbound file has an
`unboundReason`. None of the 12 tables, 12 balanced row files, 12 pre-diagonal
IRs or 12 diagonal certificates is unbound. The unbound files are:

- all 11 transport certificates. No layer publishes their hash, but the
  checker re-derives every identity they state from the included IRs. Those
  IRs are bound, except #13's two pre-transport IRs;
- #13's intermediate compiled IRs, pre-transport IRs and reduction
  certificates;
- #13's order-47 baseline raw IR;
- producer check reports, some of which carry timestamps.

`tools/assemble.py` and `tools/derive.py` record how the packet was built.
They need not be run.

## End states and layer order

The stack is a chain of local changes. Each PR's packet is unchanged in every
later head (see Sources).

| Layer | PR head | Packet under `research/` | Table(s) here |
| --- | --- | --- | --- |
| 1 | #8 `ad7fc756` | conditional-quartic-reduction | pr08-389 |
| 2 | #9 `51111cc9` | factored-pole-reduction | pr09-385 |
| 3 | #11 `e8654b2c` | scalar-chain-reduction | pr11-385 |
| 4 | #12 `772fe96a` | scalar-preparation-zero | pr12-383 |
| 5 | #13 `31563264` | detector-cube-reuse | pr13-380 and the optional pr13-383-order47 |
| 6 | #16 `59c59e55` | height-consumer-refinement | pr16-380 and the optional pr16-383-order47 |
| 7 | #17 `eb00b7c9` | mixed-detector-normalization | pr17-380 |
| 8 | #18 `ce15e8ec` | scalar-row-reduction | pr18-379 |
| 9 | #19 `32abb654` | odd-power-detectors | pr19-376 |
| 10 | #20 `75e76303` | higher-order-variant | pr20-377 |

The two end states are:

- **#19**: 376 variables and 425-digit coefficients. This is the top of the main chain.
- **#20**: 377 variables and 327-digit coefficients. It is an optional
  alternative built above #19 that spends one more variable to reduce the
  coefficients. It is not a successor that replaces #19.

PR numbers #10, #14 and #15 are not part of this stack.

### The 12 tables

`Rows SHA-256` is the SHA-256 of the decompressed plain-text rows file
`tables/<label>/rows-<n>.txt.gz`. That file is derived here, so it has no
published hash. The checker requires it to equal the bound
`balanced/integer-ir.json`. The table is bound by the file named in the last
column. For #11, #12 and #13 (both tables), the rows JSON is bound only
through the bound diagonal certificate's `newIrSha256`. For the other tables
its hash is also published directly, in EXPECTED.json or in the archive.

| Label | PR | Vars | Rows | Monomials | Max digits | Anchor | Table SHA-256 | Rows SHA-256 | Table bound by (75e76303) |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- |
| pr08-389 | #8 | 389 | 357 | 26295 | 757 | 3^2364 | `1c612d20…d35573` | `80ddbba1…06f391` | conditional-quartic-reduction/EXPECTED_OUTPUTS.json |
| pr09-385 | #9 | 385 | 353 | 26235 | 757 | 3^2364 | `47da0042…161ecf` | `f16b0d20…fe4db8` | factored-pole-reduction/EXPECTED.json |
| pr11-385 | #11 | 385 | 353 | 26200 | 682 | 3^2130 | `c9e3e65c…43bdfb` | `2629916b…388594` | scalar-chain-reduction/EXPECTED.json |
| pr12-383 | #12 | 383 | 352 | 26019 | 682 | 3^2130 | `8faea54e…183b0d` | `6a7d5e61…dfbb17` | scalar-preparation-zero/EXPECTED.json |
| pr13-380 | #13 | 380 | 349 | 26025 | 682 | 3^2130 | `373c624d…15f6e5` | `811a84d6…553bef` | detector-cube-reuse/EXPECTED.json ["45"] |
| pr13-383-order47 | #13 | 383 | 352 | 26043 | 646 | 3^2016 | `8ac84ab6…e91ebc` | `15830116…a54e72` | detector-cube-reuse/EXPECTED.json ["47"] |
| pr16-380 | #16 | 380 | 349 | 26025 | 679 | 3^2118 | `a194dd94…9a43e6` | `e82c1f34…d3c218` | height-consumer-refinement/EXPECTED.json ["45"] |
| pr16-383-order47 | #16 | 383 | 352 | 26043 | 644 | 3^2010 | `d2e9856d…8eab6f` | `0439eab9…fb61cc` | height-consumer-refinement/EXPECTED.json ["47"] |
| pr17-380 | #17 | 380 | 349 | 26025 | 644 | 3^2010 | `995c84c3…77e796` | `e1de98a2…430d2c` | mixed-detector-normalization/EXPECTED.json ["46"] |
| pr18-379 | #18 | 379 | 348 | 26021 | 425 | 3^2010 | `50167c7f…cd37ec` | `492f019c…7fcb5f` | scalar-row-reduction/EXPECTED.json |
| pr19-376 | #19 | 376 | 345 | 25964 | 425 | 3^2010 | `b2fe4f56…48b9c1` | `90ac4257…b4e2a5` | odd-power-detectors/EXPECTED.json |
| pr20-377 | #20 | 377 | 346 | 25979 | 327 | 3^1512 | `1e02fbc1…69690b` | `87ae2fc1…e6dd4a` | higher-order-variant/EXPECTED.json |

Shortened hashes show the first 8 and last 6 hex digits; `INDEX.json` has them in full.

## What `check_evidence.py` verifies

It needs Python 3.9 or later, uses only the standard library, and imports
nothing from the stack. From the repository root:

```sh
python3 -B research/stack-public-evidence/check_evidence.py --verify-bindings .
```

The recorded run is in [CHECK_OUTPUT.txt](CHECK_OUTPUT.txt). All checks
passed, in one process with Python 3.12 and about 110 MB of memory. On the
same machine, runs took 9 to 13 seconds of wall-clock time; the file gives
the exact time of the recorded run. `--verify-bindings`
needs a clone that contains `75e76303` and `452c8620`. The review-archive
commit `452c8620` is on a separate branch of the fork and is **not** an
ancestor of this packet's commit, so fetch it explicitly. From a fresh clone:

```sh
git clone https://github.com/cameronfreer/diophantine-z-q.git
cd diophantine-z-q
git checkout proposal/quartic-stack-public-evidence
git fetch origin 452c8620a47752d58b42ca44d8432a907f89fae5
git cat-file -e 75e7630341e0722aca7bca414e10b6ff003ba498^{commit}
git cat-file -e 452c8620a47752d58b42ca44d8432a907f89fae5^{commit}
python3 -B research/stack-public-evidence/check_evidence.py --verify-bindings .
```

Leave `--verify-bindings` out to skip
that step. The checker verifies the following, exactly. No floating point
decides anything.

1. **Files.** It checks `MANIFEST.json`, and the stored and decompressed
   SHA-256 and byte count of every file. It also checks that every hash
   recorded as `statedIn` really occurs in its carrier file. With
   `--verify-bindings`, it checks that each of the 452 recorded published
   hashes occurs in the named file at the named commit, using `git show`.
2. **Table.** It checks the header, the absence of repeated or zero
   monomials, and that every variable occurs. It checks degree 4,
   content 1 and an `x0^4` coefficient of 1. It checks that the number of
   variables, number of monomials, maximum digits and maximum bits equal
   the published summary. Where the summary has a `cExponent`, it also
   checks that the maximum equals `28902*3^(4*cExponent)`.
3. **Rows.** The plain-text rows equal `balanced/integer-ir.json`, term by
   term, after compaction: the table's `xk` is the IR coordinate with the
   k-th smallest id. Every row is integral and primitive.
4. **Sum of squares.** The sum of the squares of the rows is expanded with
   exact integers and compared with every coefficient of the table. They
   are equal for all 12 tables.
5. **Diagonal map.** The certificate's source and target hashes are those of
   the included IRs. For every row, it substitutes
   `old x_i = 2^a_i 3^b_i new x_i` into the pre-diagonal row at the fixed
   `S`. The result must be the stated nonzero rational divisor times the
   balanced row. The input is fixed, and the counts of scaled coordinates
   match the summary.
6. **Compiled IR to next IR.** At the fixed `S`, `compiled-ir.json` has the
   same rows as the pre-transport IR. For #8, which has no transport, the
   comparison is with the pre-diagonal IR. The coordinates that
   `coordinate-map.json` omits occur in no row. The map agrees with the IR.
7. **Factored-pole transports** (#9 and every later table) are checked as
   **algebraic identities only**. The four private slots occur only in the
   four rows of their block. Under the stated reverse lift `H=s*v`,
   `q=s*Q`, `q2=s^2*Q2`, `s2=s^2`:
   - the old `s2` row vanishes;
   - the old `Bh` row becomes a nonzero multiple of the new one;
   - the old `q2` and second-conic rows become nonzero multiples of `s^2`
     times the new ones.

   The old conic has the form `17 b q2 + 3H^2 - 2 s2 H - s2^2`, and the
   new conic has the form `17 b Q2 + 3v^2 - 2sv - s^2`, with the
   certificate's `b`. Every other row and coordinate is unchanged.
8. **Exact rewrites.** The certificates in `rewrites/` are checked; see
   below. The checker also confirms that #16's raw IRs equal #13's in every
   field except `fixedParameter`.
9. **Errata arithmetic** for [ERRATA.md](ERRATA.md).
10. **Thirteen negative controls.** These in-memory mutations must each be
    refused for the intended reason: a changed table coefficient, a changed
    row, a changed divisor or power, a corrupted lift or conic input, an
    outside consumer, a zeroed ideal multiplier, a wrong `mu`, a changed
    conic row, a wrong contact root and a changed `eSixth` row.

**Not checked here:**

- the link from `raw-translated-ir.json` to `compiled-ir.json`. The gate
  identities and the compiler's `reduction-certificate.json` are not
  replayed. The included gate-check reports are the existing evidence: they
  are bound for #11 and #12, and the archive `452c8620` holds replays for
  #16 to #20;
- that each raw IR is a faithful encoding of its PROOF.md;
- any positivity, domain, zero-branch, valuation, completeness, height or
  prime-selection argument;
- the eleven inherited inputs of
  `conditional-quartic-reduction/PR_DEPENDENCIES.md` (lines 24–40).

### Exact-rewrite certificates (`rewrites/`)

These certificates settle **algebraic identities only**.

- **#18, row changes A and tri:** `rewrites/pr18-rows-A-tri.json`. This is
  an ideal-membership certificate between the #17 raw IR and the #18 raw IR,
  over formal `S`.
  - Forward, from an old solution to a new one: `T := 42*r*W2` and
    `Bh := 184460384539620*Bh`.
  - Reverse: `W2 := N^2`, `T0 := L*N^2` and `Bh := Bh/184460384539620`.

  Each map is applied to every row of its target system. Each image must
  equal an explicit combination of rows of the other system. In particular:
  - A: `u0_new = u0 + (-39/8) g0 + 18 g1` and
    `u1_new = u1 + (9/2) g0 + (-39/4) g1`, where `g0` and `g1` are the
    `S.chart.x.0/1.definition` rows;
  - tri: `W2.definition` is deleted, and the new row is `ri*T - 42N^2`.
    The new `Bh` row is `Bh - eT`. The second conic changes only by the
    fixed rescaling `Bh_new = 184460384539620*Bh_old`;
  - `r` and `L` are decoded from the actual rows, and
    `mu*(1+k*L) = 42r` holds.

  The certificate also checks:
  - the row delta: one row deleted and five changed;
  - the coordinate delta;
  - that the inverse guards are identical.

  Since both maps fix the input, the two systems have the same rational input
  projection. This needs no positivity. The existing `check_rows.py` and its
  report `tables/pr18-379/row-check.json` cover the same claims; the report
  is bound by the archive.
- **#13, cube reuse:** `rewrites/pr13-cube-reuse-order45.json` compares #12
  with #13. `…order47.json` compares the order-47 baseline with the #13
  order-47 IR. Each certificate checks:
  - the deleted rows: the 12 rows `mixA`, `mixB`, `mixC` and `mixD`;
  - the added rows: the 9 rows `eCubed`, `eSixth` and `eTwelfth`;
  - the 3 changed `q12` rows. All other rows, the guards and all common
    named values are identical;
  - that every added, changed or deleted row is a nonzero multiple of its
    displayed definition over the IR's affine values. These are
    `e3=q1cube*delta3`, `e6=e3^2`, `e12=e6^2`, `E*q12=e12^2`,
    `mixA=E^2`, `mixB=mixA*E`, `mixC=q1cube*mixB`, `mixD=mixC^2` and
    `E*q12=mixD^2`;
  - that the alias `deltaCubed` is affine, owns no coordinate, and equals
    `(98t-1)^3` once the `t`, `Fsquare` and `Fmiddle` aliases are solved.
    `Fsquare=t^2` and `Fmiddle=Fsquare*(t+c4)+c3*t+c2` are themselves
    checked rows.

  The equivalence of the old and new systems then needs only the displayed
  substitution in detector-cube-reuse/PROOF.md, lines 67–73. Given the
  unchanged rows `q1cube=q1^3` and `E=q1*delta^2`, it gives
  `mixC=E^3 q1^3=(q1 delta)^6=e6`, so `mixD=e12`, and conversely. The
  existing `check_cube.py` and its unbound reports `cube-check.json` cover
  the same rows.
- **#9, factored-pole transports**, and the same transport in every later
  layer, are checked as algebraic identities by item 7 above.

**Still needed for these layers.** The factored-pole maps still need their
positive-domain and zero-branch arguments. These are
factored-pole-reduction/PROOF.md, lines 74–110: `b>0` gives `q=H=0` when
`s=0`. That positivity comes from the parent's own arguments, which nothing
here checks. The arithmetic-route layers #11, #12, #16, #17, #19 and #20 are
**not settled by any certificate in this packet**. The certificates here only
fix the exact rows that those arguments are about.

## Claims by layer

Each layer's claims are sorted into three kinds:

- **(a)** an exact rewrite, settled by a finite check now that the rows are published;
- **(b)** a reapplication of an existing lemma, with the place where the PROOF.md cites it;
- **(c)** a new arithmetic argument.

Line numbers refer to the files at `75e76303`. Source lines that a PROOF.md
quotes from Version 13 or the manuscripts are repeated as cited there. They
were not re-verified here.

**#8, conditional-quartic-reduction (389).** This is the base package, and
its README lists what changed.
- (a): the two-prime diagonal balancing (`proofs/diagonal_scaling_round8.tex`, §1 l.1, map l.12, rows l.61; `PR_DEPENDENCIES.md` T31 l.302), and the complete sum of squares of the final rows (part of T30, l.294). Items 4 and 5 above check these here. Item 6 checks only that the compiled IR, at the fixed `S`, has the same rows as the next IR. The compilation itself (T30's gate identities and compiler operations, `reduction-certificate.json`) is **not** replayed here; see "Not checked" below.
- (b): the 32 retained transformations T01 to T32 (`PR_DEPENDENCIES.md` l.42 onward), on top of the 11 inherited inputs (l.24–40).
- (c): primary-order promotion to order 12 for `UA.g` (`proofs/detector_round8.tex` l.1, completeness l.51, pole estimates l.133). The Euler-product refinement giving height exponent 577/32 (`proofs/arithmetic_round8.tex` l.69, l.112). The consumers at anchor `3^2364` (l.248, margins l.286).

**#9, factored-pole-reduction (385).**
- (a): the four transports' identities (PROOF l.44–72). Item 7 checks these; the existing `check_transport.py` does too.
- (b): the factored-conic template, Version 13 `addition.tex` l.595–615 (PROOF l.10–21). Positivity from `proofs/detector_round7.tex` l.117–144 and `proofs/geometry_round7.tex` l.15–49 (PROOF l.91–105).
- The zero-branch converse (PROOF l.74–90) is a short local argument resting on that positivity. It is not a finite check.

**#11, scalar-chain-reduction (385, 682 digits).**
- (a): the source row delta: 6 deleted, 6 added, 2 changed and 360 unchanged (PROOF l.65–71, `LOCAL_CHECKS.json`). Also compilation, transports and the diagonal map with `c=3^355` (l.207–220).
- (b): the two-place proxy lemma, `proofs/prior/round5/geometry_round5.tex` §l.98 and §l.147 (PROOF l.21–23, 106–118). The varying-anchor argument, `proofs/optional_anchor_height_round7.tex` §l.51. The height bound, `proofs/arithmetic_round8.tex` l.112 and l.248.
- (c): order-31 soundness by valuation descent through the chain `J3,J2,J1,N` (l.73–118). Completeness with general preparation (l.120–154). Anchor 2130 with the three height consumers (l.156–205); Carlos checked the displayed integer margins.

**#12, scalar-preparation-zero (383).**
- (a): the source delta: 3 changed rows and 1 deleted (`LOCAL_CHECKS.json`). The free omission of `preparationU` and `preparationV`, which occur in no row (PROOF l.37–44; checked by item 6). Transports and the diagonal map.
- (b): Version 13 `v5:preparation-zero-bridge` l.10563–10636. `v5:real-progression-bridge` l.10638–10694. `thm:v5-simultaneous-primes` l.16566–16604. `subsec:v9-deep-completeness` l.19727–19746. `geometry_round7.tex` l.68–92. All are as cited in PROOF l.63–76, 143–204.
- (c): the connection to the order-31 chain. Soundness (l.55–106). The finite-place preparation and the congruences of `rho` modulo 32, 243 and 17 (l.108–139); Carlos checked these. The real size and simultaneous choice of the shared point (l.141–221).

**#13, detector-cube-reuse (380, and optional 383 at order 47).**
- (a): the cube reuse (PROOF l.9–81). It is an exact local projection equivalence, and `rewrites/pr13-*` certify its rows; see above.
- (b): the arithmetic consumers are identical (l.83–104). The optional order-47 route reapplies the retained `references/precision51_PROOF.md`, verbatim from fork commit `bc51100f`, as given by `references/ORIGIN.json` (l.106–129).
- (c): none claimed. The precision-51 argument itself (valuation, CRT, completeness, poles) is an earlier argument, still unreviewed beyond the finite statements Carlos checked.

**#16, height-consumer-refinement (380/679 and 383/644).**
- (a): the generated raw systems equal #13's over formal `S`, apart from the fixed parameter (PROOF l.204–208). The packet checker checks this for both orders, and so do the included `height-check.json` reports, which the archive binds. Compilation, transports and the diagonal map.
- (b): the projective-height argument, `proofs/optional_anchor_height_round7.tex` §l.138. The varying-anchor equivalence, §l.51. `v9:lem:product` (PROOF l.10–48, 94–110).
- (c): the projective transfer at exponent `alpha=577/32` with `K0=(3H+14)/2` (l.50–92). The Lucas endpoint test with its uniform monotonicity beyond the endpoint (l.130–160). The scalar margin and final input inequality (l.162–200). The reevaluated private anchor gate and witnesses at the new `S0` (l.112–128). Carlos checked the displayed integer statements but not the monotonicity step.

**#17, mixed-detector-normalization (380/644).** This layer changes the detector normalization. The six high tests now use weight `e^91/delta^3`. That is the round-5 normalization `e^(2m-1)/delta^3` at `m=46`, through the new last gate `q1*qHigh = h^2` (PROOF l.41–53). Before, the gate was `q1^3*q45 = h^2`, the round-7 normalization `e^(2m-1)/delta` at `m=45`. The low and input tests keep `e^(2m-1)/delta`. The one-place lemma receives `d = D/delta`, `D/delta^12` and `D/delta^47` (l.77–90). The order changes from 45 to 46 and the anchor from 2118 to 2010.
- (a): the source delta: only the three `q46` rows change (`mixed-check.json`). Compilation, transports and the diagonal map.
- (b): `proofs/prior/round5/arithmetic_round5.tex` §l.90 and `proofs/detector_round7.tex` (PROOF l.10–14). The small-prime reapplication in `proofs/prior/round4/arithmetic_round4.tex` §l.91 (PROOF l.70–75). `precision51_PROOF.md` (l.119–137). #16's projective transfer (l.139–157).
- (c): mixing two normalizations within one product in the common-place descent (l.63–115). The order-46 consumers (l.126–157). Simultaneous completeness with the new pole inputs, including real infinity and `p=2,3,17` (l.159–219).

**#18, scalar-row-reduction (379/425).**
- (a): the whole layer is claimed to be algebraic. Row changes A and tri (PROOF l.36–115) are certified by `rewrites/pr18-rows-A-tri.json`. The fixed 35-coordinate diagonal map, `DIAGONAL_WEIGHTS.json` (l.137–158), is checked by item 5.
- (b): all arithmetic objects are retained unchanged (l.11–34). The transport is reapplied to the new scalar normalization (l.127–135).
- (c): none claimed.

**#19, odd-power-detectors (376/425).**
- (a): the chain `q1^6, q1^12 -> q12=q1^23, h=q1^46, q46=q1^91` (PROOF l.34–47). The report `power-check.json` covers it. Compilation, transports and the diagonal map.
- (b): the one-place proof `manuscripts/quartic_v10.tex` `lem:v5-one-place` with its small-prime reapplication (l.12–19). `precision51_PROOF.md` and #17's two-anchor application (l.108–123). The unchanged height inequalities (l.125–142).
- (c): the uniform odd-power normalization `q1^(2m-1)` in the common-place argument (l.59–106). Completeness for the changed pole inputs (l.144–205). The PROOF itself says that the private pole witnesses, `W` and `B` change (l.103–106).

**#20, higher-order-variant (377/327; optional).**
- (a): source comparisons and the new quotient rows (PROOF l.313–323; `higher-check.json`). Compilation, transports and the diagonal map with 36 weights.
- (b): the scalar norm descent and preparation-zero sources. The proxy lemma (l.15–20). #18's A/tri (l.42–48). `precision51_PROOF.md` (l.186–194). The anchor equivalence (l.263–269).
- (c): scalar order 47 via `rInverse31` (l.35–87) and scalar completeness (l.89–133). The order-50 detector chain (l.135–182) and precision-50 consumers (l.184–215). Detector completeness (l.217–259). Anchor 1512 with all height margins (l.261–311).

## Scope of Carlos Toledo's review

Carlos reviewed the finite facts of #8, #9, #11, #12, #13 and #16 at the heads
above. He checked them with independent code and decided "Incomplete review"
for each. He covered:

- **T**: each table's bytes, hash, counts and maximum.
- **N**: a necessary condition for a sum of squares: every variable has
  degree 2 or 4, with positive semidefinite Gram blocks.
- **A**: the finite statements displayed in each PROOF.
- **B**: hash bindings, ancestry and CI copies.

He did not decide:

- the sum of squares itself, or any statement about rows;
- the local proofs beyond their displayed finite statements;
- the application contracts;
- the eleven inherited inputs;
- for #13 and #16, the gate and raw-row comparisons, the transports and the diagonal maps;
- the 391/392/393-variable variants of #8.

Items 3 to 7 of the checker and the #13 certificates now give a reviewer
finite checks for several of these. They are author-side checks, and Carlos
has not reviewed them.

**#17 to #20 are outside his scope.** The archive at `452c8620` holds separate
reviews of #16 to #20. Those records describe themselves as internal AI
reviews, not human peer review and not the designated App check.

## Layout and formats

- Each table has a directory `tables/<label>/` that keeps the build-relative
  path of each file. A `.gz` suffix marks gzip compression (level 9,
  `mtime` 0, no stored name). `INDEX.json` maps each role to its file:
  - `table`: the decimal table;
  - `rowsText` and `rowsIr`: the balanced rows, as text and as JSON;
  - `diagonalCertificate`: the diagonal map;
  - `preDiagonalIr`, `transportCertificate` and `preTransportIr`: the IRs
    and certificate around the factored-pole transport;
  - `compiledIr`, `coordinateMap`, `reductionCertificate`, `compilerReport`
    and `specializationCertificate`: the compiled IR and its maps;
  - `rawIr`: the raw source IR;
  - `gateCheck`, `transportCheck`, `diagonalCheck`, `layerCheck` and
    `measured`: the existing check reports.

  A file shared by two tables is stored once. For example, #9's
  pre-transport IR is #8's pre-diagonal IR.
- `INDEX.json` also records, for every file, its compressed and decompressed
  SHA-256 and bytes, its build origins, its bindings, and an unbound reason
  where one applies. Omitted file kinds and the reasons for omitting them are
  under `omittedFromEveryTable`.
- [FORMATS.md](FORMATS.md) documents the rows text, the table and every JSON
  schema the checker reads.
- `MANIFEST.json` gives the path, bytes and SHA-256 of every file except
  itself. `CHECK_OUTPUT.txt` was recorded before it was added to the
  manifest, so the run it shows checked a manifest without it. The checker
  also accepts the final manifest.

**Omitted (see `INDEX.json`):**

- `balanced/polynomial.json`. It is the same quartic as the table, which
  `assemble.py` verified for all 12 tables, and its hash stays published.
- `compiled/polynomial.json`, a derivable sum of squares over `Z[S]`.
- `raw-ir.json`, which precedes the anchor translation.
- the active and candidate twins of included IRs.
- generator code, logs and receipts.
- #8's unselected 391/392/393 variants.

One discrepancy was found and the file was left out. The `builder.cjs` in the
#17 build directory has SHA-256 `cd0aae54…`, but
mixed-detector-normalization/EXPECTED.json lists `a2ce8241…`. The #17 raw IR,
final IR, polynomial and table all match EXPECTED.json, and so does the #18
build's `baseline/builder.cjs`. No builder is included.

The discrepancy is explained. Regenerating `builder.cjs` from #17's frozen
patches at `eb00b7c9` gives exactly the expected `a2ce8241…`. The local
`cd0aae54…` copy differs from it in three comment lines only. The local copy
was not used for any included file, and `EXPECTED.json` is unchanged.
