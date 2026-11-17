# Reuse the contact polynomial's cubic in all three detectors

This change starts from the protocol-updated #12 at
`772fe96a0e65bee76db500d8ef3a7a6b5e884d1f`. Its mathematical packet is
byte-identical to the previously reviewed preparation-zero source at
`a1f9233049cc0f8aeb2a6ccd7e7b613cec3c1ec0`. The default construction retains
all test orders, the order-31 scalar chain and anchor exponent 2130.

## An affine cubic already exists

For each detector the actual builder sets `t=A*lambda`, `delta=98t-1` and

```
F(t)=t(t-1/49)(t-1/50)(t-1/2450)(t-32/1225)
    =t^5+c4*t^4+c3*t^3+c2*t^2+c1*t+c0.
```

It stores `t2=t^2` and

```
M=t2*(t+c4)+c3*t+c2=t^3+c4*t^2+c3*t+c2
```

as `detector*.Fsquare` and `detector*.Fmiddle`, before the weights. Its
assignment routine stores the quadratic part and keeps lower-degree terms
as affine aliases. Therefore the semantic M itself is affine in existing
coordinates, as are

```
t3=M-c4*t2-c3*t-c2,
delta3=98^3*t3-3*98^2*t2+3*98*t-1.
```

The defining equations imply `t3=t^3` and `delta3=delta^3` on every solution.
Neither alias needs a new coordinate. This uses the existing Fmiddle
definition, not an unmaterialized cubic expression passed to a quadratic
gate. The checker decodes the actual affine aliases into Q[t], recomputes
the five-contact coefficients and verifies the complete cubic identity.

## Four weight gates replace five

The unchanged source has positive `q1=e/delta`, `E=q1*delta^2=e*delta=1/R`,
and the already stored cube `q1cube=q1^3`. That cube is still used by the
order-one product evaluation. The old higher-weight segment is

```
mixA=E^2; mixB=E^3; mixC=E^3*q1^3=e^6;
mixD=mixC^2=e^12; q12=mixD^2/E=e^23/delta.
```

Replace it by

```
e3=q1cube*delta3=e^3;
e6=e3^2=e^6;
e12=e6^2=e^12;
q12=e12^2/E=e^23/delta.
```

Every new defining equation has degree at most two in the stored rational
coordinates. The first multiplies a stored cube by an affine alias; the
last is `E*q12=e12^2`. The nonzero denominator E and all positivity premises
are supplied by the unchanged source domain. In particular `delta>=39/25`,
the equation `q1*F=A*(A*delta)^4` excludes F=0, and q1,E are positive.
There is no new division or condition on a point, root or pole witness.

Both directions are explicit. Given an old solution, compute the new e3,
e6,e12 uniquely by the displayed formulas. Its q12 and every later value
are unchanged. Given a new solution, restore `mixA=E^2`, `mixB=E^3`,
`mixC=E^3*q1^3` and `mixD=mixC^2`. The cubic identity and `E=q1*delta^2`
show `mixC=e6`, `mixD=e12`, and hence the old q12 equation. These maps are
inverse after projection to the common coordinates, with unique auxiliary
extensions. No cancellation by a possibly zero private pole witness is used.

The old intermediates have no consumers outside this segment. The checker
compares every actual raw equation and every guard after matching coordinate
names. Across three detectors it deletes twelve old gate rows, adds nine
new rows, changes only the three q12-definition rows, and preserves all
other rows. It separately checks that delta3 is affine and has no allocated
coordinate. The full compiler determines the saving; an affine alias is
not counted again as an eliminated polynomial coordinate.

## Arithmetic consumers are identical for the default construction

The source meanings of q1, E, q12, `mixedHigh=q12^2` and
`q45=mixedHigh^2/q1cube` agree exactly. The sixteen field tests, their
orders, all symmetric coefficients and grouped products, the reciprocal
trace and each physical detector pole input are therefore identical.
The arbitrary-order one-place lemma and its common-place conclusion consume
the same normalized factors and the same R. All finite-place hypotheses,
real bounds, small-prime preparations and opposite-place cases are retained.

The scalar input, all four norm nodes, preparation zero, both-place proxy
argument including prime 41, simultaneous real/finite completeness, fixed
anchor and all three height inequalities are unchanged. Every old tuple
has the new weight extension, so the already constructed actual shared
point H remains the same; no new simultaneous existence argument is needed.
All identity-point and conic-zero branches are preserved by the same maps.

This is a local rational projection equivalence relative to the inherited
construction. It neither repairs nor independently establishes the global
group, pole-realization, prime-pattern, height or Lucas inputs. No new
Euler-system index set or inverse limit is involved. The relevant domain
coverage is every allowed source solution and every detector block.

## Optional higher precision at the former variable count

The same exact substitution applies to the independently reviewed order-47
alternative at `bc51100fd3ada82df0dac55d6f1d235219430c74`. Its supplying
argument is preserved verbatim in `references/precision51_PROOF.md` with
its original hash and URL in `references/ORIGIN.json`. Read its actual
precision-51 tail, all primary identity branches, the primary progression
`Pi^46`, pole hypotheses and three height consumers at anchor exponent 2016.
Those are conditions of this optional alternative, not of the default 380.

The implemented optional source makes exactly the earlier order-47 changes:
the six high tests have order 47 and the anchor is `3^2016`; it uses
`highLift=mixedHigh*E`, `q47=highLift^2/q1`. The unchanged input logarithm
still has order12. The preceding route proved the actual order 47 comparison
at every retained prime and compatible completeness with scalar preparation
zero; no order 52 or additional exceptional-prime exclusion is asserted.

Now apply the cubic projection equivalence to that actual source. It leaves
q12 and mixedHigh identical and therefore also highLift and q47 identical.
Every supplying and consuming object in that argument is unchanged. Its
380-to-383 variable tradeoff is measured after full compilation; the earlier
reference's count 386 describes its source before this three-coordinate
reduction. That old count is retained in the verbatim historical proof,
not silently rewritten.

## Actual compiled outputs and coefficient maps

After the same certified omission of two unused preparation slots, exact
compiler/elimination checks, four factored conic transports and input-fixed
diagonal scaling, the outputs are:

| Route | Coordinates | Residuals | Monomials | Exact maximum coefficient |
| --- | ---: | ---: | ---: | --- |
| Default order 45, anchor 2130 | 380 | 349 | 26,025 | `28902*3^1420` (682 digits, 2266 bits) |
| Optional order 47, anchor 2016 | 383 | 352 | 26,043 | `28902*3^1344` (646 digits, 2146 bits) |

The input is fixed by both projection and diagonal maps. Every variable
occurs; each sum-of-squares quartic has degree four, integer content one
and coefficient one on the fourth power of the input. Primitive row scaling
is by nonzero rational factors; the rational zero set is preserved. The
separate diagonal checker reconstructs every row and every coefficient.
The dense affine cubic slightly increases monomial count despite reducing
coordinate count. `EXPECTED.json` binds the exact generated tables.

## Historical and review scope

The supplying cubic and weight definitions are present in the frozen
package's actual builder and explained in `proofs/detector_round7.tex`.
Earlier restricted searches did not establish global circuit minimality;
their initial monomial sets did not credit this affine cubic from Fmiddle.
This application identifies and verifies that reuse without claiming
historical priority or mathematical optimality. Prior local arithmetic
arguments are preserved and their exact consumers compared above.

Manuscript incorporation remains pending. The initial proof and application
contract are author submissions; independent decisions must bind the exact
final files separately. A passing coefficient or source checker is not
acceptance of the inherited arithmetic theorem. The protocol-v1.2 research
scope and cumulative evidence are recorded in HANDOFF.md.
