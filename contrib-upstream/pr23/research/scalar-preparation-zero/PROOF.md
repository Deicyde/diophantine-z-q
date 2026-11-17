# Scalar preparation zero: proposed application at 383 variables

Author: Codex, Cameron's session, 2026-11-08. This is an author argument
for review, conditional on the parent's inherited arithmetic inputs.
Independent acceptance and manuscript incorporation are pending.

## Exact change and consumers

The immediate parent is the order-31 chain on upstream PR #11, commit
`e3444641dffc2d1cf5a9791111d584110e5dd111`, including the four conics of
#9 and the frozen 389-variable package on #8.
`SOURCE_BINDINGS.json` records the source versions used here. All symbols
in this argument refer to the parent's actual functions, not Version 13's
different scalar norm tree.

Retain

```
beta = 2401 + 2754(2X+1)^2,
r = beta(beta-1)(32beta+343),  rho = 42r,  kappa = r^-15,
A+B sqrt(2) = f(H),  C+D0 sqrt(2) = f(R),  R=S-P,
Tproxy = Re(k_H w_S),  y = Tproxy/r^16,
J3 = D0^2 + kappa y^2,
J2 = C^2 + kappa J3^2,
J1 = B^2 + kappa J2^2,
r N = A^2 + kappa J1^2.
```

Replace `W=1+N` by `W=N`. In the scalar pole set the preparation to zero:
the physical input is `b=rho W^2`, the normalized preparation is `T=b`,
and the two free coordinates `preparationU, preparationV` disappear.
Keep a materialized `T=rho W^2` so `E(17-T)` remains quadratic. The pole's
conic coefficient after square absorption is still `rho`, not `b`.
The three detector poles, point charts, logarithms, height constants and
anchor are unchanged. Applying the four factorizations afterwards gives
383 coordinates and 352 residuals; this count was actually compiled.
The raw allocation preserves the old coordinate IDs. The compiler's
free-extension certificate removes the two unused preparation slots;
no non-scalar source row needs a new normalization.
The raw source comparison checks identical coordinate allocation, changes
only `scalar.preparationT.definition`, `scalar.Bh.definition` and
`scalar.secondConic`, and deletes only `scalar.preparationConic`.
The explicit omission bridge leaves every compiled residual unchanged
before passing its active coordinate list to the affine-search consumer.

This is **not** an equivalence of all old witness tuples: the physical pole
input changes from `rho(1+N)^2` to `rho N^2`. Soundness and completeness
must therefore be proved separately. The final four-conic transport is
still an exact local projection equivalence on its positive domain. The
compiler omission of two unused slots has a zero extension; this is a
separate algebraic operation from reconstructing the semantic old pole
witness `u=rho N`. Neither operation claims equivalence to the old
physical input `rho(1+N)^2`.

## Positivity and soundness at the actual prime domain

For every rational input, `beta>=2401` and `r>0`. The unchanged joint
`H,H-P` chart forces `g_H!=0`; hence the real coefficient of
`f(H)=g_H^2` is `A=g_0^2+2g_1^2>0`. Therefore `N>=A^2/r>0` and
`W>0`. Square absorption is invertible. No positivity is inferred from
the new pole equations, and no new inverse guard is required.

The pole with preparation zero implies the same exclusion of negative
odd valuations of the **physical** `b`. The exact source is Version 13,
`v5:preparation-zero-bridge`, lines 10563–10636. Its obstruction includes
all zero-witness cases. In the source notation, set normalized `E=17e`,
`Pnorm=p/b`, `Snorm=s/b`, `Qnorm=q/b^2`; the source second-conic
quantity becomes `b^2 E(17-b)`. Then absorb the nonzero W as below.
These scalars account for the source coefficient `17b` before the final
coefficient becomes `17rho`. Normalize its witnesses as in the parent's
`proofs/prior/round3/arithmetic_proof.tex`, then absorb `W` as in
`proofs/prior/round4/scalar_streamlining.tex`. With preparation zero,
the omitted normalized witnesses recover as `u=rho W`, `v=0`, since
`u^2=rho T`. The factored-pole reverse map restores the required second
conic, including its zero branch.

Use the parent's exception set `{2,3,5,7,13,17}`. At any consumed prime
with odd `R_p=v_p(r)`, the unchanged input-polynomial argument in
`geometry_round7.tex`, lines 68–92, gives `R_p>0`. Since `42` is a unit,
the pole implication gives

```
R_p + 2v_p(N) > 0,  hence v_p(N) > -R_p/2.
```

This is exactly the bound reached in the old proof after subtracting
one from `W`. The remaining descent is unchanged: the coefficient
valuation parities at each norm node are opposite because `R_p` is odd.
Thus the valuation is the minimum, including zero arguments with infinite
valuation. The strict bounds, as multiples of `R_p`, are

```
A > 1/4, J1 > 31/4, B > 31/8, J2 > 91/8,
C > 91/16, J3 > 211/16, D0 > 211/32, y > 451/32,
Tproxy > 963/32.
```

Both coefficients of `f(H)` and `f(R)` have positive integer valuation.
The unchanged two-place scalar proxy lemma, including its split-41
case, therefore applies to these same points and this same `Tproxy`:
`v_p(Tproxy)=v_p((a-1)/h)`. Integrality of valuations gives
`v_p(Tproxy)>=31`, and the nonzero integral index `h` gives
`v_p(a-1)>=31`. Thus the order-31 scalar height consumer in
`research/scalar-chain-reduction/PROOF.md` retains its premise and exact
margin at anchor `3^2130`. No stronger claim of order `31 R_p` is made. The detector, Lucas and final input contradictions do
not change.

## Finite-place preparation for integer input

Fix an integer `X`, so `rho` and `r` are positive integers. On the support
of `r`, retain the sufficient conditions of the order-31 chain:

```
v_p(A),v_p(B),v_p(C),v_p(D0),v_p(y) >= 16R_p+1.
```

Each inner node preserves depth at least `16R_p+1`; the root then gives
`v_p(N)>=16R_p+2`. The proxy condition is the finite bound
`v_p(Tproxy)>=32R_p+1`, imposed after fixing H. At primes dividing 42 but not `r`, and also
at 17, impose positive coefficient depth on `A,B,C,D0,y` whenever `r`
is a unit. Then `v_p(N)>=2`. These are finite formal-neighborhood
conditions; good reduction at the exceptional primes is not assumed.
Choose `H` first, and impose the conditions on `R` and `Tproxy` after
fixing `H`, as in the parent. Include any other finite continuity
conditions of the retained comparison construction.

The polynomial `rho(X)` satisfies, for every integer `X`,

```
rho = 4 mod 32,   rho = 81 mod 243,   rho = 13 mod 17.
```

Complete residue checks verify these congruences. Consequently `rho` is
a square in Q_2 and Q_3, with valuations 2 and 4 respectively, and is
a square unit in Q_17 (`13=8^2 mod 17`). Multiplication by the nonzero
square `N^2` preserves all three squareclasses. The imposed depths give
`v_2(b)>=3`, `v_3(b)>=1` and `v_17(b)>=2`. At primes dividing `rho`,
`N` is integral, so `b` has no denominator there; outside that support
its valuation is even. Hence its reduced denominator is a square.

## Real size and simultaneous choice of the final shared point

Use the source real-progression lemma `v5:real-progression-bridge`, Version
13 lines 10638–10694, and the order of choices in its preparation-zero
argument (`addition.tex`, lines 631–704). Let `G` be the closure of the
simultaneous real orbit of `P` and its conjugate, `G^0` its identity
component, and `m0=|G/G^0|`. These are the same generator and real groups
as the parent. A progression whose residue and modulus are divisible by
`m0` has dense positive tail in `G^0`; it need not be the full product
of two circles.

Choose a modulus divisible by `64m0` imposing all finite requirements
on `H0=[h0]P`, with `h0` a positive multiple. Density permits `H0`
arbitrarily close to both real identities. Then `A,B` tend to zero.
With `H0` fixed, let `R=[s]P` tend to both real identities in a sufficiently
divisible positive progression, including `6 | s`, the anchor requirement
`3^1064 | s`, and all finite conditions above. Its indices can be
arbitrarily large. The unchanged root chart has `S=P+R` near `P`, so
`w_S` tends to zero and `Tproxy=Re(k_H0 w_S)` tends to zero. Thus

```
C,D0,y -> 0,
J3,J2 -> 0,  J1 -> B^2,
N -> (A^2 + r^-15 B^4)/r,
b -> (42/r) (A^2 + r^-15 B^4)^2.
```

First choose `H0` to make the last limit less than 17/8, then choose
`R` to make the actual `b(H0,R)<17/4`. Nonzero points can be used
throughout. The parent #11 anchor requires the finite preparation `3^1064 | s`,
by the uniform even-anchor argument and its specialization at exponent
2130. No anchor equation or root choice changes in this layer.

Keep `R` fixed. Continuity gives a nonempty neighborhood of `H0` in
`G^0` with `0<b(H,R)<17`. A sufficiently divisible fixed modulus `L0`,
including `64m0`, preserves all the finite conditions under
`h=h0 mod L0`. Choose the remaining labels, roots and scales before the
contact primes, as in the parent. Shrink to an open set with compact
closure inside this neighborhood avoiding all comparison poles. The
real-progression lemma's finite-pole argument justifies that choice,
so the comparison bounds are fixed before the primes.

The exact inherited congruence connection is Version 13's
`subsec:v9-deep-completeness`, lines 19727–19746, with the parent's
primary exponent **44** in place of 19. For a fixed enlarged `L0` the
separated prime construction supplies

```
gcd(M_-,M_+)=1, gcd(M_-,L0)=16, gcd(M_+,L0)=1,
gcd(Pi,M_+)=gcd(Pi,L0)=1.
```

For the source theorem `thm:v5-simultaneous-primes` (Version 13 lines
16566–16604), take its odd squarefree `M` to contain the odd prime
divisors of `L0` other than seven. The prescribed ray condition at seven
handles that prime separately; the condition modulo 16 gives the fixed
two-adic reduction-order valuations. Its `q` may be enlarged to clear
the fixed scale denominators and the required finite congruences. The
contact forms are first made integral and repeated forms merged while
retaining their incidences, as in the parent. At least the distinct
contacts at scale one remain, so its requirement `k>=2` is met. Choose
its cutoff `Y` after the finite data, and its real bound `H` after the
uniform comparison bounds. The theorem permits every such fixed `q,M`
and fixed coefficients; no uniformity in a growing `L0` is asserted.

Since `64 | h0`, the conditions
`h=0 mod Pi^44 M_-`, `h=1 mod M_+`, `h=h0 mod L0` are compatible.
Their solution progression has residue and modulus divisible by `m0`.
Its dense positive tail meets the chosen neighborhood at arbitrarily
large indices. This supplies the parent's actual order-45 primary
depth, all retained opposite-place conditions, the scalar finite
conditions and `0<b<17` simultaneously. No contact prime is chosen
before fixing these data, and no bound is allowed to depend on a
later progression modulus.

All the hypotheses of the preparation-zero lemma now hold for this
physical `b`. It supplies new pole witnesses; normalize, absorb `W=N`
and factor the second conic using its positive coefficient `rho`.
This is the proposed completeness transfer. The inherited prime-pattern
and arithmetic existence theorems remain conditional inputs, not new
conclusions of the finite replay.

## Review status

Historical disposition: prior inputs and a preparation-zero construction
were found in Version 13; the parent norm tree requires the connecting
argument above. Current manuscript disposition: pending. The exact
application and its consumers require fresh independent review, especially
the simultaneous choice with the parent's actual scalar proxy and order-45
detectors. The stored application contract is unaccepted. The earlier 383-variable
research note used the order-28 balanced tree; this is a fresh application
to the order-31 chain, with the changed finite depths and real limit above. Finite checks
establish the displayed identities, inequalities, circuit counts and
coefficients; they do not accept this completeness argument.
