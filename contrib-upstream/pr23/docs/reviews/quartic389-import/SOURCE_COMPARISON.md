# The 389-variable import and the current pole input

Date: 2026-11-08. Author: Codex, in Cameron's import session.

This is an internal source comparison for the conditional research import at
`d8c472975d67d5f55677b3446214e5f55ed1be8a`, against upstream
`5bbd74f6a479776a332cbe036809d5dddae63720`. It records the inherited pole
interface and the existing Kato repair. It is not independent acceptance of
the 389-variable construction, a new audit of primary Kato sources, or a
complete audit of the restricted converse. The frozen package is unchanged.

[SOURCE_COMPARISON.json](SOURCE_COMPARISON.json) binds the manuscript files,
the compared excerpts and the supporting records by SHA-256. Line numbers
below refer to those exact files. Review follows the
[audit integration protocol](../../audit-history/PROTOCOL.md).

## Source statements and their consumers

The package's `pr_dependency_inventory.json` entry `G_pole` cites Version 10.
The following passages were compared directly with Version 13. All six
listed excerpts are byte-for-byte unchanged; this does **not** mean that
their supporting arithmetic proof is unchanged.

| Label | Version 10 lines | Version 13 lines | Compared text |
| --- | --- | --- | --- |
| `hyp:RC` | 1083–1089 | 1090–1096 | Theorem statement only |
| `lem:corank` | 1150–1162 | 1157–1169 | Statement and proof |
| `hyp:o8-pole` | 7704–7725 | 7711–7732 | Definition, statement and proof |
| `lem:original-seven-simultaneous-realization` | 7780–7883 | 7787–7890 | Statement and proof |
| `lem:original-seven-parity-completeness` | 7885–7933 | 7892–7940 | Statement and proof |
| `v5:preparation-zero-bridge` | 10556–10629 | 10563–10636 | Statement and proof |

Here the manuscripts are [Version 10](../../../manuscripts/quartic_v10.tex)
and [Version 13](../../../manuscripts/quartic_v13.tex). The actual argument,
including its connecting steps, was read; equality of excerpts alone was
not used as evidence of those steps.

The restricted converse concerns the non-CM family
`E_ell: y^2 = x(x-ell)(x+3ell)`, for positive squarefree `ell = 11 mod 12`,
with 2-primary Selmer corank one. It is not a statement about the package's
separate CM generator family. The corank lemma supplies the corank-one
conclusion from the 2-Selmer dimension-three calculation for a curve with
full rational 2-torsion. The simultaneous-realization proof applies this
chain to both `E_n` and `E_(n theta)` and then uses the forward rank-one
result. Its inputs include positive squarefree `beta, theta`, disjoint
supports away from 2 and 3, the stated congruences modulo 24, and the mutual
local-square conditions; the `theta = 1` case is included.

The parity-completeness proof constructs these inputs from positive `b`
with square reduced denominator and the required squareclasses at 2, 3
and 17. With `B = 17b`, it selects `U` and uses the squareclasses of `B`
and `B(B-U^2)`. This is the connecting argument to the seven-witness
formula `Psi(b)`. The pole implication rules out negative odd valuations
outside `{2,3,17}`. The preparation-zero specialization additionally
requires `0 < b < 17` and `v_2(b) >= 3`, `v_3(b) >= 1`, `v_17(b) >= 2`.
Those extra hypotheses must not be dropped when selecting its consumer.

The package consumes this interface in
[`construction/builder.cjs`](../../../research/conditional-quartic-reduction/construction/builder.cjs),
function `pole`, through the normalized conics

```
17 b P^2 = (17-E)(17+3E),
H = E(17-T),
17 b Q^2 = (s^2-H)(s^2+3H).
```

Its retained normalization argument is in
[`proofs/prior/round3/arithmetic_proof.tex`](../../../research/conditional-quartic-reduction/proofs/prior/round3/arithmetic_proof.tex).
It uses rational changes of variables with nonzero input `b`: the old
`e,p,s,q` are respectively `bE,bP,bs,b^2Q`, with `T=U^2/b`. The two old
conic residuals become `b^2` and `b^4` times the normalized residuals.
This identifies the formula being consumed, rather than just its name.

For the detector blocks,
[`detector_round7.tex`](../../../research/conditional-quartic-reduction/proofs/detector_round7.tex)
establishes the domain and constructs the physical input `B=n^2/E>0`
before invoking the pole formula. Its completeness construction makes
`B<17` and gives the required three valuation lower bounds, so these
blocks use the preparation-zero specialization. The promotion in
[`detector_round8.tex`](../../../research/conditional-quartic-reduction/proofs/detector_round8.tex)
changes the primary local test, while retaining completeness depth 45.
Checking that new detector argument in full remains separate from this
source comparison.

For the scalar block,
[`geometry_round7.tex`](../../../research/conditional-quartic-reduction/proofs/geometry_round7.tex)
uses physical input `b=42rW^2`, with `r>0` and `W=1+N>=1`.
Square absorption makes the coefficient in the normalized conics `42r`,
while the preparation input remains `42rW^2`; these are distinct objects.
The proof uses the general preparation argument and preserves its local
squareclasses. It does not invoke the `b<17` specialization for this input.
A proposed scalar preparation-zero optimization would therefore change
the argument and require a new review.

## Where the Kato repair enters

The relevant historical arguments are the Version 11
[arithmetic audit](../../manuscript-revisions/version11/evidence/arithmetic.md),
[interface audit](../../manuscript-revisions/version11/evidence/interface.md)
and [independent review record](../../manuscript-revisions/version11/evidence/independent-review.md).
Their actual index and norm arguments were read, together with the current
manuscript passage; their acceptance labels were not substituted for that
comparison. The original Kato articles were not re-audited in this session.

Version 13's existing
[application contract](../../manuscript-revisions/version13/kato-carryforward-application.json)
binds construction lines 12314–12455, application lines 12677–12787 and
consumer lines 12626–12676. Its
[acceptance record](../../manuscript-revisions/version13/kato-carryforward-acceptance.json)
belongs to that application, not to this new research package. The repaired
connection is:

* Set `N_K=2Nd` and `N'_K=c d_s`, with coprimality supplied by the smoothing
  conditions. The extended K8 construction allows every positive `m`
  coprime to `c d_s`, hence every index required by the 1999 definition:
  `N_K | m` and `gcd(m,N'_K)=1`.
* For `ell | m`, construction supports agree and corestriction has factor
  one. For a new prime `ell`, divisibility by `N_K` makes it good and
  unramified, and the factor is
  `P_ell(ell^-1 sigma_ell^-1)`, where
  `P_ell(X)=1-a_ell chi(ell)X+ell X^2`. Arithmetic Frobenius and inverse
  deck action have different roles. Smoothing primes are excluded from
  the indices, not added to the inverted support.
* Equal supports at `D N_K 2^n` and `D 2^n`, and transitivity through the
  common upper field, give
  `cor(y_(N_K 2^n))=y_(2^n)` on the cofinal tail `n>=1`. There is no
  additional Euler factor or field-degree scalar. The divisor parameter
  in Kato's definition is one, distinct from the conductor's odd part `d`.
* The integral lattice comparison uses at most a fixed factor `2^c_E`.
  It is a unit at the away-from-two localizations actually used. Thus the
  limiting class has the coordinate ideal `J` consumed by K15, rather
  than merely being a proportional class. The subsequent full-open to
  `j_*` cohomology comparison remains the one in the existing contract.

This is the earlier repair supporting the unchanged restricted-converse
statement. The comparison found no changed hypothesis in the six listed
pole-interface statements. It does not establish all eleven inherited
input groups in the package or independently validate the whole
restricted-converse proof.

## Disposition and remaining review

Historical disposition: **prior justification found** for the repaired
index-domain and class-identification interface. Manuscript disposition:
the existing repair is incorporated in Version 13; incorporation and
acceptance of the **389-variable construction are pending**.

Before incorporating the proposal as an accepted manuscript construction,
review its detector, scalar, height and diagonal-scaling arguments at their
actual consumers, complete the dependency comparison, and obtain the
application contracts and independent acceptance required by the protocol.
This note supplies neither a new acceptance record nor authority to reuse
an old approval for a revised route. The frozen Version 10 citations remain
historical evidence; this external note supplies their current comparison.

The PR's additional CI job verifies the source inventory, runs all 23
reproduction stages and checks the resulting manifests and finite reports.
Those checks establish only the properties implemented by the checkers.
They do not prove the inherited global arithmetic theorem.
