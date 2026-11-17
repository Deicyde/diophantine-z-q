# coeffrows: lowering the 682-digit maximum by changing equations (380 coordinates)

Author: exploration agent, 2026-11-09. Not reviewed. No arithmetic acceptance claimed.
Base: #13 order 45, E=2130, 380 coordinates, 349 rows, 682 digits (28902*3^1420).

## Why the two rows bind (S = 3^2130)

- `scalar.shiftedS.rootTimesInverseRoot.definition.{0,1}` is the K-equation
  w*(xP*xS + D) = hP*hS*jS - xS*jP, with w = h_S*tau (Q = S-P). It has both
  `xS` (from -xS*jP) and `xS*w` (from w*xP*xS). The diagonal LP therefore forces
  weight(w) <= spread.
- `anchor.physicalA.definition` is S*t = N(w) + 3S*N(B0+X rho) with N the norm of
  Q(sqrt2). The conic tests t in Z_(2) cap Z_(3), i.e. v3(w) >= E/2. So 2*weight(w) >= 1-spread.
  Together these give spread 1/3, matching NEXT_PR.md.

## Candidates (all 380 coordinates, 349 rows, degree 4, content 1, x0^4 coefficient 1)

These are MEASURED with an exact balancer and an adapted copy of the independent checker:
`measure/balance_weights.py` and `measure/check_diagonal_weights.py`. Both are copies of the
package scripts, changed only to read the diagonal map from a JSON file and to allow negative
3-powers. The checker reports PASS for all four. Weights come from a two-phase LP
(`measure/weights.py`) and are rounded to integers.

| Id | Change | Spread (S units, LP) | Digits | Bits | How built |
|---|---|---|---|---|---|
| A | Inline xS=hS^2 in the two w-definition rows | 9/41 | **451** | 1496 | full #13 pipeline (`runs/vA`) |
| B600 | A, plus the leaf scales 3^-600 on f(Q)_1^2 in chain3 and f(Q)_0^2 in chain2 | - | 418 | 1386 | full pipeline (`runs/vB`) |
| B | A, plus S^-1 on both f(Q) leaves | 1/5 | 411 | 1363 | pipeline A, then post-compile row edit (`runs/postB_S1`) |
| C | B with S^-2, plus anchor N(f(Q)) with S^2 replacing N(w) with S | 2/11 | 373 | 1239 | pipeline A, then post-compile row edit (`runs/postC_S2`) |

The compile stage rejects constants beyond about 3^1340. Its specialization sign bound fails
first. Its affine search also rejects S multiplying quadratic monomials. So B and C with S-power
leaf scales were applied after compilation to A's final IR. Row identity between the post-edited
rows and builder semantics has been checked only by inspection.
Control: `runs/v0` reproduces the #13 final IR sha 6c18...fc53 exactly.
Pipeline A's final IR equals the hand edit `greedy2_ir.json` row for row.

## Soundness and completeness

**A.** This is a pure row operation. The new row equals the old row plus 39*(x0 def) - 144*(x1 def),
and the second row uses 36 and -78. `measure/check_rowop.py` checks this exactly and reports PASS.
The common zero set over any ring is identical, and the semantic definition of w is unchanged.
Remaining obligations:
- Bind the builder edit in `subtractRootConstant`, which replaces Qp.x with hS*hS in the numerator.
- Update the gate metadata and the reproduction and expected hashes.
- Obtain an independent check of the new diagonal map. 35 coordinates are scaled; a cleaner map is possible.

No arithmetic input changes.

**B.** The new rows are chain3 = S^-1 D0^2 + kappa y^2 and chain2 = S^-1 C^2 + kappa J3^2.
- Soundness: the valuation descent uses only primes p outside {2,3,5,7,13,17}, where S is a unit.
  The coefficient valuations, parity and the strict-bound table are therefore unchanged.
  Positivity, N>0 and W>=1 are also unchanged, because the factors are positive.
- Completeness: this needs a new argument at p=3, which divides 42 and also r. The sufficient
  depths for C and D0 become v3 >= (16R+1+E)/2 instead of 16R+1. This is still finite. Q is
  chosen after H, and the anchor domain only bounds 3^1064 | a-1 from below.
- Both the scalar-chain PROOF.md completeness paragraph and the scalar pole squareclass step
  (W must be a unit at 3) must be re-reviewed for the changed rows.

**C.** C carries all of B's obligations. In addition, the anchor becomes
t = N(f)/S^2 + 3N(B0+X rho), with conic constant 2S^4 and translated term 8S^2*U.
- At 3: v3(N(y)) is always even, because 3 is inert in Q(sqrt2). The two summands therefore still
  have opposite parity, so B0 and X are integral before oddness. After oddness, f = (w/hS)^2 with
  hS a unit, so v(f) >= E iff v(w) >= E/2. The domain is the same.
- At 2: v(f) = 2(v2(a-1)) + 3 > 0, so the old -6X^2 argument goes through.
- Since f is nonzero (guard), N(f) is nonzero.
- Still to do: rewrite round-8 "retained even anchor" for N(f), and re-run the quaternion criterion
  on 3t^2-2. The criterion only depends on t, so this should be unchanged.

## Negative results (LP, S-spread model)
- An f-anchor alone is worse: 2/5 on the base IR and 18/47 after A. The chain rows pin f.
- Chain offsets without A give nothing (1/3). f-anchor plus offsets without A gives 2/7.
- After A, no single constant row operation and no further gate inlining improves 9/41.
  The search was greedy, over binding rows: `lp/rowops.py` and `lp/greedy2.py`.
- Pure S-power offsets on the kappa term, rather than the f term, are worse (464 digits or more).

## Floor for this circuit
After C the binding rows are w-def, the S chart x0 definition, the S chart equation, f-def and the
anchor. These follow a ladder: the constants bound the chart weights, w reaches at most 2z, f
reaches at most 2w+z, and the anchor needs 2f >= 2-z. Together these give z >= 2/11.

This means a coefficient around S^(4/11), about 3^775, or roughly 370 digits at E=2130. Below that,
one needs a further existing coordinate with exact anisotropic depth doubling; none was found.
For example, the chain nodes have X-dependent 3-adic valuations. The other option is new
coordinates, which this task excludes. With the w-anchor only, the floor is 1/5, about 409 digits.

This is an LP floor relative to these rows and diagonal 3-power maps, not a theorem about all circuits.
At the other session's E=2118, the digits scale by about 2118/2130 (ESTIMATED).

## Files
- lp/: lp.py (S-spread LP), variants.py, greedy*.py, rowops.py, offsets.py, maxweight.py, explain.py
- measure/: precise_lp.py, weights.py, balance_any.py, balance_weights.py, check_diagonal_weights.py, check_rowop.py, postedit.py, offrange.py, *_weights.json
- pipe/research/coeffrows/reproduce_variant.py (copies of #13 research dirs under pipe/)
- runs/{v0,vA,vB,postB_S1,postC_S2}/ (builder, IRs, balanced tables, check reports)
