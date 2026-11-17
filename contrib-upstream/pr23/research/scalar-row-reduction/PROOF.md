# Exact scalar row reduction above #17

This conditional local construction starts from #17 at
`eb00b7c9c5be2e8666c0403c750c6c780cf78563`. It combines two algebraic
changes found by the user-supplied Opus exploration with an explicitly
specified rational diagonal map. The result has 379 coordinates including
the input and coefficients of at most 425 decimal digits. The inherited
arithmetic interpretation remains conditional. No new current manuscript
or unconditional theorem is asserted.

## Actual source and retained domain

Work over Q and K=Q(rho), rho^2=2. The actual fused subtraction chart in
the package's round-five geometry argument defines w=h_S*tau by

```
F*w = h_P*h_S*j_S - x_S*j_P,   F=x_P*x_S+D,
x_S=h_S^2,   x_S*f(Q)=w^2,    Q=S-P.
```

Here D=11-6rho, h_P=-1+7rho/4, x_P=57/8-7rho/2,
j_P=39/8-9rho/2. On the retained domain F is totally positive and
h_S is nonzero. The same shifted-point guard excludes Q=O, and the
old chart covers S=-P and all permitted chart signs. This layer changes
no field point, index, real or finite-place condition, logarithm, scalar
proxy, detector weight, contact radical or anchor parameter. In particular
the actual proxy remains Re(k_H*w), whose two-place proof handles 41.

The parent scalar-preparation-zero proof uses the positive input
beta=2401+2754(2X+1)^2, r=beta(beta-1)(32beta+343)>0 and norm-tree
output N>0. Its physical pole input is 42rN^2, while the second conic's
coefficient after square absorption is 42r. These are different objects.
The order-31 scalar conclusion, order-46 detector tests and anchor 3^2010
retain their exact meanings and all three height consumers from #17.

## A: constant row operations at the actual normalization

Replace x_S by h_S^2 only in the numerator of the defining equation for w.
The denominator F and both x_S=h_S^2 rows remain. Thus w and its f(Q),
proxy and anchor consumers are unchanged on every solution.

Let g0,g1 denote the actual raw S.chart.x.0/1.definition residuals, and
u0,u1 the old raw scalar.shiftedS.rootTimesInverseRoot.definition.0/1 rows.
The new rows are exactly

```
u0_new = u0 - (39/8)*g0 + 18*g1,
u1_new = u1 + (9/2)*g0 - (39/4)*g1.
```

The checker decodes all four rows over the actual named coordinates and
verifies these polynomial identities. Since g0,g1 remain, subtraction of
the same combinations recovers the old system. The identity map on
coordinates therefore gives equality of zero sets over Q. No division by
a variable, new square-root choice or changed chart domain is introduced.
The multipliers refer to these raw row normalizations, not the differently
scaled integers displayed in some exploratory notes.

## tri: the private scalar witnesses in both directions

Write ri for the retained scalar.rInverse coordinate, e for normalized_e,
Z for the old scalar.W2.quadratic and T0 for the old normalized
preparationT.quadratic. The actual old rows are

```
r*ri=1,   Z=N^2,   T0=L*Z,   Bh_old=e*(Z+k*T0),
k=521079743268/81331739215,
L=inputProduct + (606992616/851437489)*rPair1
               + (1211348736/851437489)*rThree.
```

The same raw rows give

```
r=4391913917610 + 28138306136472*inputProduct
                + 20059891973568*rPair1
                + 40032653027328*rThree,
mu=184460384539620,   mu*(1+k*L)=42*r.
```

The new implementation removes Z, uses one new coordinate T, and defines

```
ri*T=42*N^2,    Bh_new=e*T.
```

Because r*ri=1, T=42rN^2 is uniquely forced. This follows directly from
r(ri*T-42N^2)-T(r*ri-1)=T-42rN^2. Thus T is the physical input; it is
not identical to the old slot T0. The forward map from old solutions is

```
T=42*r*Z,    Bh_new=mu*Bh_old.
```

The reverse map from new solutions is

```
Z=N^2,    T0=L*N^2,    Bh_old=Bh_new/mu.
```

The displayed identity mu(1+kL)=42r proves both Bh equations. The actual
new second-conic residual, after Bh_new=mu*Bh_old, is exactly the old
second-conic residual. In particular its Bh^2, Bh*s2 and e*Bh coefficients
change from 3mu^2, 2mu and -102mu to 3, 2 and -102. All other coefficients
are identical. This constant normalization is essential to the transport.

No other residual consumes Z,T0,T or Bh: the checker scans every row for
these private coordinates. All outside residuals, gate expressions and
actual inverse guards agree after identifying coordinate names. The two
maps are inverse on solutions and fix every outside coordinate, including
the input, N, r, e, the field chart, the proxy and all detector quantities.
Only the already enforced r*ri=1 is used to deduce T; mu is a fixed nonzero
rational. N=0 and e=0 cause no algebraic failure of these maps, although
the arithmetic domain independently gives N>0. No permitted conic zero
witness is removed.

## Composition with compilation, conic transport and diagonal scaling

The two source changes commute: A uses the shifted chart's defining rows,
and tri uses private scalar pole slots. Their combined map preserves the
parent rational input projection in both directions. Every equation remains
quadratic. Exactly five common raw rows change and one disappears; 358
other raw rows agree. The complete compiler gate and elimination certificates
are replayed. The same two unused preparation slots have a free extension
and are omitted by the parent's checker.

Apply the four conic transports anew to the actual compiled normalization.
The supplying factored-pole proof distinguishes the physical scalar input
42rN^2 from the positive conic coefficient 42r. Both are unchanged, as are
the three positive detector inputs. The transport checker derives the
current affine encoding of H=E(17-T) from the rows instead of copying old
constants. For nonzero s, v=H/s and Q=q/s give its forward map; when s=0,
positivity forces H=q=0 and v=Q=0 supplies the zero branch. The reverse map
H=sv,q=sQ works for every s. No new arithmetic or nonvanishing hypothesis
enters this application.

DIAGONAL_WEIGHTS.json specifies 35 coordinate factors. For each old
coordinate z_i set z_i=2^(b_i)*3^(a_i)*new_z_i, using the listed integers
(a_i,b_i) and zero for every unlisted coordinate. The input factors are
zero. Every factor is a nonzero rational, including negative powers.
Substitute this map into every quadratic residual, clear denominators and
divide by its nonzero integer content. The resulting primitive rows have
the same rational zero set under the invertible diagonal map. Their sum
of squares vanishes over Q exactly when every row vanishes.

The separate checker reconstructs the specified factors and independently
normalizes rows by taking coefficient ratios, then clearing their
denominators. It reconstructs every coefficient of the full sum of squares
and parses the complete decimal table. No LP solver or floating-point
calculation is needed to reproduce or verify this chosen map. The exploratory
LP's putative optimum and any general coefficient optimum are not claimed.

The output has 379 active coordinates, 348 quadratic residuals, degree
four, 26021 monomials, content one, input fourth-power coefficient one and
maximum coefficient size 425 digits / 1410 bits. EXPECTED.json supplies
exact full-table and intermediate hashes; the complete expansion is
generated by the runner. The finite measurements are distinct from the
inherited global arithmetic interpretation.

## Historical and review status

The fused subtraction and preparation-zero inputs are prior arguments,
located and read in the versioned parent packets. The user-supplied Opus
agents proposed A and tri; their exact original notes and source scripts
are retained in prior-investigation. Codex checked the constant Bh transport,
integrated the changes above #17, supplied this proof and selected the
exact diagonal map. The old fixed-row scaling obstruction does not apply
after A changes those rows; it was never a universal bound on circuits.

This new composition requires its own non-author review. Earlier review
acceptance is not rebound. Current-manuscript incorporation, inherited
global source closure and designated App authorization remain separate.
HANDOFF.md and FINDINGS.json preserve the rejected and unfinished leads
without representing their measured polynomials as proved arithmetic
constructions.
