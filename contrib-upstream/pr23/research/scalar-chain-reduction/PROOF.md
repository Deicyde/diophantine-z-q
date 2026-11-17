# Order 31 at the same scalar coordinate cost

Author argument, 2026-11-08, Codex in Cameron's session. Independent review
and manuscript incorporation are pending. The inherited global arithmetic
inputs remain conditional. This is a changed application of the scalar
method, not an independent proof of those inputs.

## Sources and exact objects

Start from upstream PR #9, commit
`6fd131e7ca150d7a023bcb6ac4f1971912705fab`, and the frozen package on #8.
The actual earlier norm argument is `proofs/geometry_round7.tex` in that
package, especially its odd-contact, norm-descent and finite-preparation
sections. Its earlier search record is
`evidence/geometry/rejected-paths-round7.txt`; the later record is
`evidence/round8/scalar/scalar-search-notes-round8.txt`. They discuss
restricted searches, not general lower bounds on circuits. The arguments
in these sources were read. This proposal does not claim historical priority
or identify a defect in their selected construction.

The proxy source is `proofs/prior/round5/geometry_round5.tex`, sections
“A scalar test using only a local approximation to the ratio” and
“A uniform two-place trace argument, including the prime 41”. It explicitly
permits every positive scalar order. The height consumers are in
`proofs/arithmetic_round8.tex`, and the anchor for varying even exponent
is justified in `proofs/optional_anchor_height_round7.tex` together with
the round-eight anchor discussion. Exact versions are in SOURCE_BINDINGS.

Use the same field K=Q(sqrt(2)), nonidentity points H=[h]P and
Q=S-P=[a-1]P, chart functions, input and scalar proxy:

```
beta = 2401 + 2754(2X+1)^2,
r = beta(beta-1)(32beta+343),  rho = 42r,  kappa = r^-15,
f(H) = A+B sqrt(2),  f(Q) = C+D0 sqrt(2),
Tproxy = Re(k_H w_S),  y = Tproxy/r^16.
```

For every rational X, r>0. Retain the explicit inverse of r and the three
steps producing r^-3, r^-7, r^-15. Retain both coefficients of f(H), both
coefficients of f(Q), and the shifted-point guard f(Q)_0 * inverse = 1.
In particular a-1 is still nonzero. No claim about the proxy is used to
establish the formal-group premises it requires.

## Chain and quadratic cost

Replace the old balanced tree by

```
J3 = D0^2 + kappa y^2,
J2 = C^2  + kappa J3^2,
J1 = B^2  + kappa J2^2,
r N = A^2 + kappa J1^2.
```

Keep W=1+N and physical pole input b=rho W^2 in the main candidate.
This uses the original general preparation, with its U,V,T witnesses.
Each of the four nodes uses one right-square coordinate and one output:
eight rational coordinates, exactly the old cost of the left subtree plus
the two right norm nodes. The root equation rN=A^2+kappa*J1Square is
quadratic, because the square is stored. Its only denominator is the
already positive r. All chain outputs are nonnegative, N>0 because the
unchanged joint chart gives A>0, and W>=1.

The source comparison identifies coordinates by name, including the old
`scalar.N.quadratic` and the new `scalar.N` output role. Six defining rows
are replaced and the two N rows change. All 360 other raw rows agree under
that identification; the separate fixed parameter changes below. The
generic compiler and exact elimination pipeline retain the same count.
This is a new soundness/completeness construction, not a bijection between
the old and new scalar witnesses for fixed outside data.

## Valuation descent on the actual prime domain

Let p be a consumed prime outside {2,3,5,7,13,17}, with odd R=v_p(r).
The unchanged polynomial argument gives R>0: a pole of X gives
v_p(r)=6v_p(X), an even integer; integral X makes r integral.
The pole obstruction gives v_p(W)>-R/2. Since 0=v_p(1)>-R/2,
N=W-1 also satisfies v_p(N)>-R/2, without assuming noncancellation in W.

At the root the two summand coefficient valuations in
N=A^2/r+r^-16 J1^2 are -R and -16R. They have opposite parity.
Each inner node has coefficient valuations 0 and -15R, again of opposite
parity. Thus its valuation is the minimum of the summand valuations.
The convention v_p(0)=infinity handles zero leaves.

Successive strict lower bounds, in multiples of R, are

| Object | Strict lower bound divided by R |
| --- | ---: |
| A | 1/4 |
| J1 | 31/4 |
| B | 31/8 |
| J2 | 91/8 |
| C | 91/16 |
| J3 | 211/16 |
| D0 | 211/32 |
| y | 451/32 |
| Tproxy | 963/32 |

Both rational coefficients of each f(H) and f(Q) have positive integer
valuation. At the odd unramified prime this implies positivity at every
place of K above p, including both split places. The existing curve and
nonzero charts therefore put these same points in the formal group.

The source proxy argument now applies: k_H/k_Q=((a-1)/h)u with
u=1 modulo p^4 at every place. The recovered chart gives
w_S*k_Q=-h_P modulo p even at the nonunit fixed-coordinate place above 41.
Taking the rational trace gives a unit U0=1 modulo p and
Tproxy=((a-1)/h)U0. Consequently

```
v_p(Tproxy) = v_p((a-1)/h) > (963/32) R >= 30 + 3/32.
```

Integrality gives v_p(Tproxy)>=31, and the nonzero integral h then gives
v_p(a-1)>=31. For the same radical as the parent,
M_S(beta)^31 divides a-1. This is not a claim of order 31R.

## Completeness with general preparation

Fix any integer input. All constants r,kappa are fixed rational numbers.
At a prime p dividing r, put R=v_p(r)>=1. Sufficient conditions are

```
v_p(A), v_p(B), v_p(C), v_p(D0), v_p(y) >= 16R+1.
```

If both inputs have depth at least 16R+1, the inner expression
u^2+r^-15 v^2 has depth at least 17R+2, hence at least 16R+1.
Induction through the three nodes, then division by r at the root,
gives v_p(N)>=16R+2. At p dividing 42 but not r, and at 17 when r is a unit, require positive
depth of the five inputs. The inner outputs and N then have depth at
least two. Thus N is integral on the support of rho and W=1+N is a unit
there. Outside that support the physical b=rho W^2 has even denominator
valuation. Its reduced denominator is a square and its local squareclasses
are the same as the parent's, since W is a nonzero rational square factor.
The retained general preparation lemma supplies the scalar pole witnesses.

These stronger conditions are still finite. Choose H sufficiently deep
first for A and B; after H is fixed choose Q deeper for C,D0 and Tproxy.
The source proxy completeness argument gives Tproxy -> 0 as Q -> O,
with H fixed, also at exceptional primes. Here the condition on y means
v_p(Tproxy)>=32R+1, a finite bound. Require also the anchor divisibility
specified below. Once S is fixed, finite continuity in H preserves these
conditions on a sufficiently divisible progression. Roots and positive
square scales are then fixed before the unchanged separated contact-prime
selection and final primary congruence Pi^44 | h.

This uses the same quantified permission for arbitrarily large finite
preparation in the parent. It does not add a real smallness condition:
W>=1 retains the parent's general preparation route. The scalar norm
change does not alter the comparison tests or the detector orders 1,12,45.
The source global existence and prime-pattern inputs remain conditional.

## Smaller anchor and all three height consumers

Retain exactly the parent's proved height exponent and constant:

```
alpha = 577/32,
Hheight = 3*2^106*(2^32*3^9)^6*46410^18 + 128.
```

Use even anchor exponent E=2130 rather than 2364. The prior varying-anchor
argument gives the same point/input domain except for the finite condition
0 != a-1 in 2*3^1064 Z. All four labels remain odd, and X remains integral
at 2 and 3. Its noncircular order first derives root parity from the
product's leading residues and then applies the formal index formula.
No chart, guard, quaternion form, packing coefficient or input map changes.

The retained 2-integrality excludes X=-1/2, so beta differs from 2401;
its positivity excludes the other exceptional values 0,1,-343/32 of the
height theorem. Thus the same height bound applies to the actual beta.

Set c*=2*3^1064 and b*=3^1064. Every solution has c=|a-1|>=c* and
|a|>=c*-1>=b*. The exact checker verifies

```
(c*)^415 > (4 Hheight)^992,
(b*)^143 > (24 Hheight)^360,
100*670 < b*,   b* > 152.
```

The first is the scalar margin for order 31: since
1-alpha/31=415/992, h(beta)<=Hheight*c^(alpha/31)<c/4.
The second is the parent's unchanged sufficient Lucas margin at order 45,
where 2-4alpha/45=143/360. Explicitly, the parent's transfer and |F|<5B^4 give
B^(143/360)<24Hheight if the literal Lucas polynomial F is nonzero;
the checked endpoint gives the opposite bound for every B>=b*.
Thus F=0 and its retained theorem gives log B>|a|-3.

For n!=beta the unchanged order-12 input comparison and alpha<19 give

```
log B < (12/5) log(40 Hheight) + (19/5) h(beta)
      < (487/500)|a| + 19/20 < |a|-3.
```

Here the exact inequality 40 Hheight<2^670 implies log(40 Hheight)<670, and the checked b* bound
supplies log(40 Hheight)<|a|/100. The same c/4 bound and |a|>152 justify
the remaining steps. This checks the actual scalar, Lucas and input
consumers separately. It does not substitute an exponent into an unproved
general theorem. The final inference X integral is the parent's unchanged
one. Completeness permits the new finite condition 3^1064 | a-1.

## Factoring and coefficient replay

Apply #9's four conic factorizations after compilation. The same positivity
of rho, W and the three detector inputs supplies all zero branches. The
transport checker reconstructs the actual new compiled normalizations;
no old affine normalization constant is assumed for a newly allocated slot.

Since 2130=6*355, the parent's diagonal map applies with c=3^355. Every
factor is nonzero, the input is fixed, and every normalized residual is
primitive integral and quadratic. The separate original checker replays
every diagonal substitution and every coefficient. The measured result is
385 variables, 353 residuals, 26,200 monomials and maximum coefficient
28902*3^1420 (682 digits, 2,266 bits). All variables occur, the polynomial
has degree four and content one, and the coefficient of x0^4 is one.

## Review boundary

Historical disposition: prior norm, proxy, finite-preparation, varying-anchor
and height inputs found; the chain arrangement and its connection to the
actual consumers are supplied here as an author proposal. Manuscript
disposition: pending. The source search did not establish historical
priority or exhaust all past packets. No theorem application has been
independently accepted, and no current manuscript or acceptance record is
changed. Finite replay verifies the displayed circuit and integer margins;
it does not certify the uniform arithmetic proof or inherited dependencies.
