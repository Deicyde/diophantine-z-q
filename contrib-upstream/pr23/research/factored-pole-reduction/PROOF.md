# Four-conic transport: application proof for review

Author: Codex, Cameron's session, 2026-11-08. Independent acceptance pending.
The source is the freshly reproduced, compiled 389-coordinate quadratic IR,
SHA-256 `1e9071816ccb40d562545be08f21ccac76813a64796173d155d0d3ae7dbebb50`.
The application contract binds this proof and the source evidence. This is
a rational projection-equivalence argument conditional on the unchanged
parent domain. It does not re-prove the global arithmetic dependencies.

## Historical source and normalization

Version 13's `docs/manuscript-revisions/version13/addition.tex`, subsection
“Factored poles and the preparation conic”, lines 595–615, supplies the prior
argument. Its detector uses `H=17F`; its coefficients 867 and 34 are the
coefficients 3 and 2 below after this normalization. The older transport
report at
`quartics/quartic-394-411/sources/work/quartic-under400-20261107/02-squares/REPORT.md`
also records the four factorizations separately from scalar preparation.
The historical argument was read, including its positive-input zero branch.
This application must be reviewed anew because its source rows and stored
normalizations differ.

The parent's `construction/builder.cjs`, function `pole`, defines the second
conic by

```
H = E(17-T),     s2 = s^2,     q2 = q^2,
17 b q2 + 3H^2 - 2s2 H - s2^2 = 0.
```

The three detectors use the positive semantic input `b=B=n^2/E`. The scalar
uses the positive **coefficient** `b=42r` after square absorption; its physical
input to the original pole formula is `42rW^2`. The preparation variable
`T` retains that physical input. The transport changes neither object.

In the compiled IR, the coordinate named `.Bh.quadratic` is not literally
`H`. For each detector `H=17E-h`. For the scalar,
`H=-184460384539603 E-1181808857731824 h`. Here `h` denotes the stored
`.Bh.quadratic` coordinate, and `E` the corresponding `.normalized_e` coordinate.
The producer reads these affine expressions from the IR values; the checker
derives them separately from the actual second-conic coefficients. It checks
the entire old polynomial before applying the transport.

## Constructed equations and maps

Retain `s` and replace the private `H,q,q2,s2` representation by `v,Q,Q2`:

```
E(17-T) = s v,
Q2 = Q^2,
17 b Q2 + 3v^2 - 2s v - s^2 = 0.
```

The old slot for `h` stores `v`, the slots for `q,q2` store `Q,Q2`, and
the old `s2` coordinate and defining row disappear. Substituting the actual
affine encoding of `H` into its definition yields the first equation. All
three resulting equations are quadratic in the retained coordinates. The
first conic and the preparation equations are unchanged.

For every new solution, set

```
H = s v,     q = s Q,     q2 = s^2 Q2,     s2 = s^2.
```

If `H=alpha h+rest` is its compiled affine encoding, reconstruct
`h=(s v-rest)/alpha`. Each fixed rational `alpha` above is nonzero. The old
second-conic residual becomes `s^2` times the new one. The old `q2` residual
also becomes `s^2` times the new square residual, and the old `s2` residual
vanishes identically. The old `H` definition is precisely the new definition,
up to a fixed nonzero row normalization. Thus the new system reconstructs
the old one for **every** `s`, including zero; no cancellation is used.

Conversely, start with an old solution on the unchanged positive-input
domain. If `s != 0`, choose `v=H/s`, `Q=q/s` and `Q2=q2/s^2`. The old square
row gives `Q2=Q^2`, and the old second conic divided by `s^2` is the new
conic. The definition of `H` gives the remaining new row.

If `s=0`, the old square rows and conic imply

```
17 b q^2 + 3H^2 = 0.
```

Since `b>0` in the real embedding, `q=H=0`. Choose `v=Q=Q2=0`.
Every new row then vanishes, including `E(17-T)=0`. The old affine slot `h`
need not be zero; its reconstruction uses `H=0`. No inverse guard is added
and no zero branch is deleted. These maps preserve the projection onto all
outside coordinates, rather than claiming a bijection of private witnesses.

## Required input and domain coverage

The positivity needed for the old-to-new zero branch is established by
unchanged parts of the parent:

* `proofs/detector_round7.tex`, “Nonzero domains and quadratic degree”,
  lines 117–144: the positive chart and `q1 F=A U^4` give `F,q1,E>0`.
  The factor product is at least one in both real embeddings, so `W0>=1`,
  `N(W)>0`, `n=N(W)/(2W0)>0`, and `B=n^2/E>0`. The round-8 promotion retains
  positive weights and square tests on this same domain.
* `proofs/geometry_round7.tex`, lines 15–49: for every rational input,
  `beta=2401+2754(2X+1)^2>=2401`, hence
  `r=beta(beta-1)(32beta+343)>0`. Its norm tree gives `W=1+N>=1`.
  In `construction/builder.cjs`, the scalar square absorption therefore
  uses a nonzero `W`, and its conic coefficient is `42r>0`.

All these objects and the rows establishing them are outside the replaced
private slots. The coefficient field is Q throughout. No finite-prime
exception, index set, local approximation order or arithmetic theorem is
changed. There is no inverse limit in this local algebraic application;
the relevant identity is exact reconstruction of the old private witnesses
and preservation of the same outside input and pole coefficient. The
inherited Kato application remains conditional on the parent's stated
dependencies and is not newly accepted by this argument.

## Consumers, scaling and finite evidence

For each prefix `detector0`, `detector1`, `detector2`, `scalar`, the checker
searches **every old residual** for occurrences of the four private slots.
Their consumers must be exactly `.Bh.definition`, `.s2.definition`,
`.q2.definition`, `.secondConic`. It checks all reconstructed residual
identities up to nonzero rational constants and requires all 341 outside
rows to remain unchanged. The input coordinate and fixed parameter
`S=3^2364` also remain unchanged. Twelve rows change and four disappear,
giving 385 coordinates and 353 residuals.

The unchanged parent diagonal-scaling producer applies thirteen nonzero
rational coordinate factors, fixes the input, and divides each residual by
its nonzero rational content. The separate parent checker reconstructs all
these substitutions and verifies every coefficient of the sum of squares.
Over Q, a sum of rational squares vanishes exactly when every summand does.
Thus the reconstructed quartic has the same input projection as the old
system on its inherited domain. Its 26,235 monomials and coefficient bound
are measured finite properties, not a proof of that domain's global
arithmetic interpretation.

Historical disposition: prior justification found for the factored-conic
template. Current application: proof and finite implementation supplied for
review; independent acceptance and manuscript incorporation pending. No
prior acceptance record is rebound or copied into this packet.
