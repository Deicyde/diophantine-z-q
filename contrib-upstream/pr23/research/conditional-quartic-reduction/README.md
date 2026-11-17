# Proposed quartic with 389 total variables

This additive research proposal supplies a fully explicit integer quartic in
**389 total variables, including the distinguished input**: one input and
388 existential witnesses. It includes the construction, local proof notes,
dependency inventory, exact coefficient table, and separately authored finite
checkers. Its upstream reference is commit
`036cebe4f1a4aa7ca89820a9b48f3629b4c364d6`.

The proposed identification of its rational zero projection with the integers
remains **conditional on the inherited global arithmetic inputs** in
[PR_DEPENDENCIES.md](PR_DEPENDENCIES.md). The computations establish finite
algebra and coefficient statements. The written local arguments have received
internal AI-assisted review; they have not received independent human peer
review or a complete Lean verification. Manuscript incorporation is pending.

## The selected result

The selected table is
[tables/quartic-389-balanced-decimal.txt](tables/quartic-389-balanced-decimal.txt).
Every coefficient is an ordinary signed decimal integer. Each noncomment
line contains a coefficient, a tab, and a monomial; summing those lines defines
the polynomial. The input is `x0`. There is no unevaluated coefficient
parameter and no quantified witness for the fixed anchor integer.

| Property | Exact value |
| --- | --- |
| Total variables / existential witnesses | 389 / 388 |
| Quadratic residuals whose squares are summed | 357 |
| Total degree | 4 |
| Nonzero ordinary monomials | 26,295 |
| Maximum absolute coefficient | `28902 * 3^1576` |
| Maximum coefficient size | 757 decimal digits; 2,513 bits |
| Integer content | 1 |
| Coefficient of `x0^4` | 1 |
| Active variables | All 389 |
| Fixed source anchor | `S0 = 3^2364` |
| Additional eliminations after the generic compiler | 0 |

The largest coefficient's full decimal expansion occurs in the table. The
table is 1,050,826 bytes and has SHA-256
`1c612d20915667dfd81a7895f8d93231d5efeaf86ecfaa15194408d298d35573`.

Relative to the immediately preceding research package, the selected result
uses three fewer variables and three fewer quadratic rows, has six fewer
monomials, and lowers the largest coefficient from 905 to 757 digits. Those
comparisons concern local research packages; they do not imply upstream
acceptance of an intermediate construction. No minimality or priority is
claimed.

## Alternatives produced by the same build

The selected form minimizes the variable count among the variants supplied
here. Optional constant chains trade additional witnesses for smaller
coefficients. Their rows, maps, full polynomial JSON and decimal tables are
regenerated and independently checked.

| Form | Total variables | Residuals | Monomials | Maximum digits | Maximum bits |
| --- | ---: | ---: | ---: | ---: | ---: |
| Direct, balanced; selected | 389 | 357 | 26,295 | 757 | 2,513 |
| Direct, before balancing | 389 | 357 | 26,295 | 2,273 | 7,549 |
| Two-coordinate constant chain | 391 | 359 | 26,304 | 752 | 2,498 |
| Three-coordinate constant chain | 392 | 360 | 26,307 | 323 | 1,072 |
| Four-coordinate constant chain | 393 | 361 | 26,310 | 151 | 501 |

For comparison with the previous package:

| Comparable form | Previous variables / maximum digits | Current variables / maximum digits |
| --- | ---: | ---: |
| Selected balanced form | 392 / 905 | 389 / 757 |
| Two-coordinate chain | 394 / 888 | 391 / 752 |
| Three-coordinate chain | 395 / 381 | 392 / 323 |
| Four-coordinate chain | 396 / 178 | 393 / 151 |

The current 392-variable chain is a different polynomial from the previous
392-variable selected table. Only the current 389-variable balanced decimal
table is committed. [EXPECTED_OUTPUTS.json](EXPECTED_OUTPUTS.json) records
the deterministic outputs and generated audit reports required from a fresh
build; its explicit exclusions identify reports containing timing or other
diagnostic fields whose complete bytes are not deterministic.

## What changed in this package

### Available primary depth removes three detector coordinates

The input primary reciprocal coordinate `UA.g` previously had requested
order one. Completeness already constructs `U_A = [n]H`, with `H` at formal
depth at least 45. Integral formal-group multiplication preserves that
depth, including the identity case. Requiring order 12 for `UA.g` therefore
uses depth already present in the completeness construction.

This puts `UA.g` and the existing order-12 input cross test in a uniform
pair. Its product uses `q12^2`, already stored for the high-weight chain,
and deletes the separate `q1*q12` coordinate in each of three detectors.
All alternate point tests keep their existing orders. The new order list is
`45,12,1,1,1,1,1,1,1,1,12,45,45,45,45,45`.

The soundness argument obtains stronger premises at the same common place;
it does not assume `U_A = [n]H` for arbitrary solutions. The proof also checks
the real and small-prime completeness limits, the reciprocal trace at both
places, positivity, and the unchanged order of choices. See
[proofs/detector_round8.tex](proofs/detector_round8.tex). An independent
conservation checker compares all 362 unaffected source equations with a
freshly generated copy of the frozen round-seven source.

### A sharper height application permits `S0 = 3^2364`

The arithmetic argument improves the use of the Euler product in the
inherited modular-curve degree estimate and retains its more precise genus
bound. It obtains the contact-height exponent `577/32`, replacing 19, with

```text
C_cond = 2^32 * 3^9
H = 3 * 2^106 * C_cond^6 * 46410^18 + 128.
```

This `H` has 665 bits. The argument is a checked reapplication of the
inherited geometry, conductor, modularity and height inputs. It is not an
independent proof of those global inputs or a substitution into their final
theorem statement without revisiting its estimates.

The scalar, Lucas-label and input-label consumers are rechecked at orders
28, 45 and 12. The selected anchor becomes `S0 = 3^2364`, retaining the even
anchor argument, the same symbolic anchor equations and packing coefficient
three. Its local domain includes `a-1` nonzero and divisible by
`2 * 3^1181`. The proof keeps the noncircular local order at 3 and then 2.
See [proofs/arithmetic_round8.tex](proofs/arithmetic_round8.tex).

### Two-prime balancing reduces coefficients without new variables

Put `c = 3^394`, so `S0 = c^6`. The selected map rescales thirteen existing
coordinates by nonzero rational factors. Twelve have the retained ternary
factors `c`, `c^2` or `c^4`. Two have dyadic factors: the stored real
coefficient of `x(S)` has factor two, and
`heightProduct.scale0.quadratic` has factor `2^-21`. The two lists overlap
in one coordinate. The input is fixed.

Substitute this bijection in every quadratic row, clear its rational
denominators and divide by its signed integer content. The resulting
primitive integer rows have the same common rational zero set after
decoding. Their sum of squares therefore has the same existential
projection to the input. Five row divisors are noninteger rationals, so the
certificate records both numerator and denominator.

Decode coordinates before applying semantic point or scale identities.
For example, the old semantic height scale is `A = C0^2 = 4*x238`. After
`x238 = 2^-21*y238`, it is `A = 2^-19*y238`; the new stored `y238` need not
itself be a rational square. The transformed equations recover exactly the
old square scale needed by the detector argument.

The complete map, its inverse, row normalization, and exact maximum
`28902 * 3^1576` are proved and checked in
[proofs/diagonal_scaling_round8.tex](proofs/diagonal_scaling_round8.tex).
The independent checker imports no producer or compiler and reconstructs
every row and every output coefficient using a separate normalization and
expansion algorithm. A floating-point search suggested the map; the
delivered construction and its checks use exact standard-library arithmetic.

### Retained reductions and domains

The contact-unit detector normalization, complete identity/tangent charts,
shared logarithm circuits, and scalar outer constant `W = 1+N` are retained.
The scalar order is still 28. Its actual input remains
`beta = 11016*X^2 + 11016*X + 5155` and
`r = beta*(beta-1)*(32*beta+343)`.

The dependency inventory identifies which earlier arguments remain active
and which numerical examples or candidate variants have been superseded.
In particular retain both-place formal premises, the split-41 case, the
nonzero shifted-point guard, complete conjugation, and the order of witness
and contact-prime choices. The old optional odd-anchor appendix remains
outside the selected even-anchor construction.

## Reproduce from fresh outputs

Requirements are **Python 3.11 or newer and Node.js**. The mathematical build
uses their standard libraries, performs no package installation, and requires
no network once the repository and package are available. Run without Python
`-O` or `PYTHONOPTIMIZE`; exact audits use assertions.

From the repository root:

```sh
python3 -B research/conditional-quartic-reduction/reproduce.py --check-source
python3 -B research/conditional-quartic-reduction/reproduce.py
python3 -B scripts/check_audit_history.py
```

The first command checks the supplied snapshot. The second creates a fresh
directory under the repository's `build/`, copies only declared source/proof
inputs, and runs the complete **23-stage pipeline**. To choose a location,
pass `--output /absolute/path/to/a-new-empty-directory`. A nonempty output
directory is rejected; output must be outside this proposal directory.

The pipeline builds 400 source coordinates and 368 rows, compiles to 389
coordinates and 357 rows, checks all 339 gate identities and 330 compiler
operations, specializes the fixed anchor, constructs the optional chains,
and reconstructs all delivered quartics. It also checks source conservation,
detector assignments, the scalar and geometry equations, arithmetic bounds,
parameter binding, cross-stage bridges, and the diagonal transformation.

### What constitutes successful reproduction

The wrapper requires a successful child process and a structured
`pipeline-completion.json` containing the exact ordered 23-stage sequence
and the bound pipeline hash. It then checks every required deterministic
artifact, successful audit report, and regenerated committed coefficient
table. Both the supplied source snapshot and its copied working inputs must
still match their original hashes after the build.

The wrapper writes `reproduction-receipt.json` and prints its location. Keep
that receipt, `pipeline-completion.json`, `pipeline-progress.json`, and
`construction.log` when reporting a run. The receipt records the actual
source, build-input, artifact and report inventories for that snapshot.
Hashes bind the reviewed files and reproduction; they do not replace the
mathematical arguments.

An earlier run lacked the final stdout marker; its cause was not established.
The marker is now diagnostic information. A structured completion record
and all source/artifact/report checks determine success. A printed marker
alone cannot make an incomplete or failed build pass. Focused wrapper probes
exercise these cases separately from the real mathematical reproduction.

## Review the mathematics and provenance

Start with [proposal_note.pdf](proposal_note.pdf), then read
[PR_DEPENDENCIES.md](PR_DEPENDENCIES.md) and the machine-readable
[pr_dependency_inventory.json](pr_dependency_inventory.json). The inventory
records 32 retained transformations, 11 inherited input groups and 30 bound
proof texts. Review the
primary-order promotion at its completeness and common-place consumers;
the refined height estimate at all three comparisons; and the diagonal map
with its decoded semantic values. Then follow the inventory into the retained
local proofs and inherited global arguments.

[PROVENANCE.json](PROVENANCE.json), [ATTRIBUTION.md](ATTRIBUTION.md), and
[evidence/README.md](evidence/README.md) record source lineage, upstream
credit, AI contributions, and the scope of internal reviews. Historical
proofs and receipts are preserved as historical material, with obsolete
parameters distinguished from the selected construction.

The repository's manuscript, version designation, Lean development and
historical audit register remain subjects of their own integration and review
protocol. This directory is a research proposal; it does not designate an
official version 11, record maintainer acceptance, or represent a public
submission. Manuscript integration requires the connecting arguments at the
actual consuming passages and appropriate new review bindings.

To rebuild the review PDF after editing its source, use a LaTeX installation
supporting `proposal_note.tex` and run `pdflatex` twice in this directory.
The Python/Node mathematical build does not require TeX or reproduce PDF
bytes. No human peer review, complete Lean certification, priority or
minimality claim follows from a passing finite build.
