# Independent audit of Jose Brox's 196-variable construction

Audited on 15 November 2026 against commit `5c35db3253a70b0875acec4b451cdaac4da3c8fd` of `JoseBrox/diophantine-z-q_improvements`.

## Verdict

No error found in the 198-to-196 reduction, its complete finite specification, or either coefficient presentation. The two systems have an input-preserving bijection of rational zero sets for every fixed `N >= 1`. The defining threshold and all inherited arithmetic premises are exactly those of Conant's 198 construction. This audit does not independently re-prove those premises.

No manuscript or release target was changed. Elliot requested an audit of 196; the last direct release instruction still selects 198. Fable's relay reports a proposed change of target, but under the relay rules that report is information rather than authorization.

## Sources and method

The mathematical source is `papers/quartic/laurent_elimination_20261115_v38.tex`, especially Sections 2, 3 and 5. The finite specification is `computation/quartic/laurent_recovery_v38/config196.json` and `family196/`. The audited parent is `sources/h10_quartic198/circuits/inverse198/quadratic.json`.

All 29 downloaded files were authenticated against the pinned Git tree's blob identities. `FETCH.json` records their SHA-256 hashes. The parent is byte-identical to the frozen Conant package already used for Version 18, with SHA-256 `c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad`.

I read the proof and wrote `independent_audit.py` using Python's standard library and exact rational arithmetic. It imports and runs none of Jose's or Conant's producer/checker code. The coordinate map was independently transcribed from the paper by semantic coordinate names and compared with the supplied configuration. The supplied row multipliers were treated as certificates to verify, not as trusted conclusions. Every coefficient identity was checked, rather than sampled at numerical points.

Fable's report was read as prior audit information. The computations reported here are separate from Fable's computation and reproduce its conclusion.

## Why the deletion is valid on every solution

The parent coordinates deleted are 80 and 95. They store `w_0^4` and `w_1^4/R`, respectively. The remaining coordinates are rescaled by nonzero rational constants and fixed integral powers of `R`, `w_0`, and `w_1`. The input coordinate and these three base coordinates are fixed.

The possible failure would be a new solution with a zero rescaling quantity. Nine equations are literally retained after renumbering. Their content was checked directly, in addition to checking preservation.

Write `u = X^2`, let `v` be the first scalar-product coordinate, and let `J` be the contact-product coordinate. Three of these rows give

```
u = X^2,
4v = 6255001 + 255102u + 2601u^2,
RJ = (51X^2+103)(51X^2+2503)(51X^2+2504)(1632X^2+80471).
```

The last identity was independently expanded from the actual rows. Every factor is positive for rational `X`, so `R` and `J` are nonzero on every new solution. The forced-prime row also gives

```
R = A r(X)/(1 + 22201 r(X)) > 0,
```

where `A = 149^(2N+1)` and `r(X)` is the displayed positive product. The detector rows give `q_j w_j = 1`, so each `w_j` is nonzero. The square rows give `R_2 = R^2` and `w_{j,2} = w_j^2`.

Consequently all diagonal substitutions are invertible over the rationals. Each of the 182 retained parent rows becomes a nonzero Laurent monomial times the delivered quadratic row, modulo only those retained power relations. Both removed rows become identities after restoring the uniquely determined fourth powers. This proves both directions and covers the entire solution set, including exceptional point configurations already allowed in the parent. It adds no completeness restriction and no arithmetic assumption.

## Exact checks

| Check | Result |
|---|---|
| Parent table versus frozen Conant table | Byte-identical |
| Paper's coordinate weights and nine constant scalings versus configuration | Exact match |
| Ordered coordinate map | Parent order with precisely 80 and 95 deleted |
| Retained row identities | 182 of 182 passed |
| Deleted defining rows | Both become zero identities |
| Nonvanishing and power guard rows | All nine literally retained and checked against their stated formulas |
| Rows | 182 primitive integer quadratics |
| Coordinates | 196 including input, all occur |
| Sum-of-squares reconstruction | Every coefficient agrees with the supplied quartic, in both presentations |
| Degree and content | Degree 4 and content 1; the coefficient of `X^4` is 1 |
| Nonzero coordinate monomials | 2,943 for every integer `N >= 1`, in both presentations |
| Balanced transformation | Every row identity verified |
| Deliberate corruption controls | Changed coefficient, row shift, and primitive multiplier all rejected |

The run passed 48,690 assertions, many of which check serialization and individual coefficient profiles. The substantive coverage is the complete row and coefficient comparison summarized above. `RESULT.json` contains every row identity's source and target indices, all input hashes, and the measured results.

## Coefficients and the Busy Beaver presentation

For the unbalanced family, the parameter is `A = 149^(2N+1)`. The only terms with positive parameter degree are, using the delivered one-based coordinate indices,

```
-2 A x_102,
-44402 A x_102^2 x_114,
A^2 x_102^2.
```

There are no mixed coefficient profiles that could cancel for a special positive value of `A`. The largest constant coefficient is

```
K_fixed = 484991541504995159662206970923766531374664106904986910720.
```

Thus the exact unbalanced height is

```
H(P_N) = max(K_fixed, 149^(4N+2)).
```

The coefficient crossover is `N = 7`, since `149^26 < K_fixed < 149^27`, while the squared-parameter exponent is `4N+2`. This is not a defining threshold.

The paper's headline polynomial uses a different, balanced presentation with `C = 149^N`. Its exact height is

```
11903780636513165769654680680436132271178681610029854792 * C^2.
```

The upper bound, an attaining coefficient, and noncancellation were checked for all `C >= 149` by exact coefficient comparisons. These formulas must not be conflated.

If the separately established 198 theorem uses the fixed parameter `N = BB(2^1000)`, the same `N` works for 196 because the input projections agree for each parameter separately. The existing strict coefficient bound by `BB(2^2000)` carries over to the unbalanced presentation: its large-parameter height is the same `A^2`, with a smaller constant-coefficient maximum. This audit verifies the transfer; it does not re-prove the underlying Busy Beaver threshold theorem.

## Limits

- This is an audit of the new algebraic reduction and its exact tables. It is not a new full audit of the inherited elliptic-group, prime-pattern, contact-height, or pole-realization theorems.
- The 258-variable explicit construction and the conditional 78-variable construction in the same release were not audited here.
- The publisher's CI reports and producer programs were not needed for acceptance of the checked identities and were not executed.
- No claim of global minimality is made.

The result supports accepting 196 as a valid reduction of the audited 198 construction, with precisely the same inherited mathematical dependencies.
