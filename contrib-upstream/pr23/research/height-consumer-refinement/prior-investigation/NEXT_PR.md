# Next mathematical PR above #13: sharpen the height consumers

Research notes, 2026-11-08. Author: root Codex agent. Not independently
reviewed; no PR opened and no existing branch changed in this investigation.
Target source: `31563264ba3dfbc3f00b4b08c099e9380caacd42`.

## Concrete candidate

| Route | #13 | New parameter evaluation |
| --- | --- | --- |
| Order 45 | 380 coordinates, 682 coefficient digits, E=2130 | 380 coordinates, 679 digits, E=2118 |
| Order 47 | 383 coordinates, 646 coefficient digits, E=2016 | 383 coordinates, 644 digits, E=2010 |

The new tables were expanded from #13's actual final integer IR with only
the declared fixed parameter changed, then diagonally balanced. This is a
parameter evaluation, not a fresh end-to-end candidate reproduction. The
separate diagonal checker passes for both. Polynomial degree, content,
active variables, input fourth-power coefficient and monomial counts agree
with #13. See `anchor2118/` and `anchor2010/`, including their exact tables,
summaries, diagonal certificates and independent-algorithm checker reports.

Table SHA-256:

- E=2118: `a194dd94682d4e458d0e03407e39aea056a6626014210c384b3a9c80f19a43e6`
- E=2010: `d2e9856dcbd752a156548e37545f48ed8e1e8d263c5b374aad5a19f44f8eab6f`

## Mathematical route requiring review

Retain alpha=577/32 and
H=3*2^106*(2^32*3^9)^6*46410^18+128.

The frozen package's `proofs/optional_anchor_height_round7.tex`, section
"Projective height of the three retained scales", already proves the
projective argument for the actual scales 1, C0^2, (C0+C1)^2. It gives
h(C) <= 3T/2 + log(7)/2 from the three individual height bounds <=T.
Its old exponent 19 is used only in the supplied T, not in this inference.
The current `proofs/arithmetic_round8.tex`, "Apply the new height bound to
the actual consumers", supplies T=(H+log50)|N|^(alpha/k) on those same
objects and deliberately does not use this optional improvement.
Consequently the proposed reapplication is

    B^2-6 < ((3H+14)/2) |N|^(alpha/k).

Read the actual projective proof, field-product height proof and the
current input/consumer passages; the old optional verdict cannot approve
this new application. Keep the product in Q(sqrt(2)), not its rational norm.
Retain every inherited arithmetic premise.

For the Lucas polynomial use the exact triangle bound
P(B)=2B^4+6B^3+5B^2+1. Put c*=2*3^(E/2-1), b*=c*-1. The sufficient exact
test is

    [2(b*^2-6)]^(32m) > (3H+14)^(32m) P(b*)^577.

Its ratio is increasing for B>sqrt(6): factor out B^(64m-2308), with
positive exponent for m=45,47; the numerator's remaining factor increases
and the denominator's decreases. Thus checking b* treats all B>=b*.
At m=45, E=2118 passes; E=2112 fails this specific sufficient comparison.
The existing scalar c/4 margin and final input contradiction remain valid.

For the order-47 alternative, use the exact exponent in the final input
consumer instead of replacing alpha by 19. It gives

    log B < (384/191) log(40H) + (577/191) h(beta).

The weaker scalar target h(beta)<8c/25 suffices, since

    log B < (4712/4775)|a| + 4616/4775 < |a|-3

for |a|>=301, using log(40H)<|a|/100 and c<=|a|+1. The exact scalar test
is 8^992*c*^415 > (25H)^992. At E=2010 it passes, and the Lucas comparison
also passes. E=2004 fails this scalar test. These are boundaries of these
particular estimates, not optimality results. `height_margins.json` records
the exact integer evaluations and the separate auxiliary bounds.

The even-anchor equivalence requires only the weaker finite divisibility
3^1058 | a-1 or 3^1004 | a-1. Existing completeness indices already meet
the respective stronger old requirements. The conic witnesses can be
resupplied by the same varying-anchor equivalence. No root, scale, test,
logarithm, scalar norm or contact-prime selection changes.

Historical status: prior projective argument located; proposed application
to the current exponent and consumers pending review and incorporation.
Required PR work: bind an application contract, integrate these arguments,
run the full candidate reproductions, obtain non-author review, and publish
the cumulative handoff and exact artifact/readback records.

## Bounded circuit probes: no variable saving found

`grouping_probe.py` compiled four versions against the actual cubic-reuse
source. Counts before the unchanged four pole factorizations were:

- Baseline: 384 coordinates, 353 residuals.
- Move H and L1-beta tests to order 12: 387, 356.
- Promote two other primary tests to order 45: 384, 353.
- Promote all three other primary tests to order 45: 387, 356.

These are compiled counts, not complete candidate certifications or new
arithmetic acceptance. No global optimum or exhaustive allocation search
is claimed. Results and generated sources are preserved in `grouping/`.

## Exact obstruction to improving the leading scaling exponent alone

`scaling_lp.py` optimizes the largest exponent spread in the fixed quadratic
residual rows under arbitrary powers-of-S diagonal rescaling, fixing the
input. Floating search finds 1/3; rational reconstruction and an exact dual
certificate establish that value for this restricted problem.

The lower bound reduces to two actual rows. Let w be the exponent assigned
to `scalar.shiftedS.rootTimesInverseRoot.0` and z the maximum row spread.
The row `scalar.shiftedS.rootTimesInverseRoot.definition.0` contains both
`S.chart.x.1.quadratic` and its product with that coordinate, hence z>=w.
The row `anchor.physicalA.definition` contains its square and S times the
fixed input, hence z>=1-2w. Adding twice the first inequality to the second
gives 3z>=1. The current scaling attains z=1/3.

This is a bound for unchanged residual rows and powers-of-S diagonal
scalings. It does not rule out improved constants, changed equations,
non-diagonal maps, new anchors or better circuits. See `scaling_dual.json`
for the six nonzero rational multipliers and `scaling_solver.npz` for the
search output. This new bound has not received non-author mathematical review.

## Larger follow-up research target

Seek an order-46 or order-47 detector with the same coordinate budget as
the current order-45 detector, using the actual affine aliases and shared
product powers. Success would combine the 380-variable circuit budget with
the smaller-anchor coefficient regime. No such circuit has been found in
this investigation; this is a research target, not a predicted saving.
