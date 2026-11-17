# Sharper height consumers at unchanged variable counts

This conditional research contribution starts from #13 at
`31563264ba3dfbc3f00b4b08c099e9380caacd42`. It changes only the fixed anchor
parameter: 2130 to 2118 for the order-45 circuit, and 2016 to 2010 for its
order-47 alternative. All field tests, scalar norm nodes, pole equations,
contact primes and logarithms retain their meanings. The supplying global
arithmetic inputs are inherited, not independently established here.

## Sources and the actual objects

The source height bound is the argument in the frozen package's
`proofs/arithmetic_round8.tex`, especially “The precise inherited height
inputs”, “Reapply the Jacobian and isogeny-height bounds” and “Apply the new
height bound to the actual consumers”. Keep

```
alpha = 577/32,
H = 3*2^106*(2^32*3^9)^6*46410^18 + 128,
exceptional primes = {2,3,5,7,13,17}.
```

For the actual scalar input beta=2401+2754(2X+1)^2, the order-31 argument
in `research/scalar-chain-reduction/PROOF.md`, retained by preparation zero,
gives M(beta)^31 dividing a-1. This is divisibility by the radical to order
31; no stronger claim proportional to each odd contact valuation is used.
Set c=|a-1|>0. The same height theorem therefore gives
h(beta)<=H*c^(577/992). Its domain is satisfied: beta>=2401; equality would
require X=-1/2, excluded by the anchor's 2-integrality. Thus beta avoids all
four exceptional finite parameters 0,1,2401,-343/32.

Write K=Q(rho), rho^2=2, and C=product x(Q_i)=C0+C1*rho for the four
retained roots Q_i=[n_i]P, with labels n,a,t,b. Their labels are odd by
the anchor argument, before any use of the product-height identity. Set
U=C0+C1 and B=max(|n|,|a|,|t|,|b|). The actual three scales in the builder
are 1,C0^2,U^2. Their inherited lower bounds C0>=193 and U>=61 ensure they
are positive and nonzero. The actual positive lambda makes all three
height arguments and the projective tuple below defined.

The optional package proof `proofs/optional_anchor_height_round7.tex`,
“Projective height of the three retained scales”, supplies a stronger
transfer argument. We rederive its application at alpha below. Its earlier
use of exponent 19 is not silently substituted into a theorem statement.
The odd-product argument is `docs/quartic-523-540/addition.tex`,
`v9:lem:product`: its proof checks each finite place, the exceptional place
above seven and both real embeddings. It concerns the product in K, not
the rational norm, which could cancel valuations at different split places.
These inherited applications and their sources remain qualified as before.

## Projective transfer at the current exponent

Let N be any nonzero integer divisible to order k by each of the three
actual detector contact radicals. The round-eight argument supplies

```
h(lambda), h(C0^2*lambda), h(U^2*lambda)
    <= T=(H+log(50))*|N|^(alpha/k).
```

Use normalized absolute logarithmic heights. Projective scale invariance,
coordinatewise squaring and the placewise maximum inequality give

```
2*h([1:C0:U]) = h([lambda:C0^2*lambda:U^2*lambda])
             <= h(lambda)+h(C0^2*lambda)+h(U^2*lambda) <= 3*T.
```

Indeed, at each place log max_i |y_i| is at most the sum of
log max(1,|y_i|). The projective scaling step uses the product formula;
lambda is nonzero, and the tuple [1:C0:U] cannot vanish. These operations
use rational coordinates with the same absolute normalization over K.

Now C=(1-rho)C0+rho U. Both coefficients are integral at every finite place.
At the two real embeddings the operator bounds relative to max(1,|C0|,|U|)
are 2*sqrt(2)-1 and 2*sqrt(2)+1, whose product is 7. Consequently

```
h(C) <= h([1:C0:U]) + log(7)/2 <= 3*T/2 + log(7)/2.
```

The actual odd-product identity bounds each root height by h(C), and the
inherited root lower bound gives B^2-6<h(C). Since log(50)<4, log(7)<2
and |N|^(alpha/k)>=1, the new transfer is

```
B^2-6 < K0*|N|^(alpha/k),  where K0=(3*H+14)/2 < 7*H.
```

Every positive integer k for which the supplying divisibility is proved
is covered. The consumers here are the actual Lucas residual at k=45 or
47 and the reduced input numerator at k=12. The scalar height inequality
uses beta itself and remains the separate inequality stated above.

## The anchor domain and both completeness constructions

For even E, the unchanged packed anchor with S0=3^E is equivalent, on the
retained point/input domain, to oddness of all four labels, X integral at
2 and 3, and

```
0 != a-1 in 2*3^(E/2-1)*Z.
```

The source is the exact varying-anchor equivalence in the optional
round-seven proof and the noncircular derivation in round eight. It first
deduces odd labels from the product's 3-adic leading residues, then uses
the formal multiple formula. It covers both signs of a-1, zero summands
in the packed norm and the retained tangent/sign branches. The translated
anchor is related by the same invertible affine change of its three
witnesses. No new quaternion or pole theorem is invoked.

Set c*=2*3^(E/2-1), b*=c*-1. Every solution has c>=c* and B>=|a|>=b*.
The selected exponents give 3^1058 | a-1 or 3^1004 | a-1. The old
completeness constructions already impose respectively 3^1064 or 3^1007.
Keep their actual shared H, root points, real neighborhoods and finite
progressions, including the preparation-zero requirements and, for order
47, the precise identity branches and depth construction in
`detector-cube-reuse/references/precision51_PROOF.md`. Every such old tuple
satisfies the weaker new point/input anchor condition. Reevaluate the
private `anchor.physicalA` gate, namely the packed norm expression, at the
new S0. The equivalence supplies three conic witnesses for that new value;
apply the same affine witness translation with the new S0. These gate and
witness values are private to the anchor; no other construction consumes
them. There is no claim
of a bijection between conic witness tuples or between old and new allowed
scalar indices. Completeness therefore uses the same simultaneous choices,
not a limit point or a separately chosen H. Soundness on the larger new
domain is provided by the following inequalities.

## Lucas contradiction, uniformly beyond the endpoint

The actual residual is F=t^2-a(a-2)tb+(a-2)^2 b^2-1. The unchanged
integrality and label comparisons give the three radical divisibilities
to order m=45 or 47. For all B>0 its triangle bound is

```
|F| <= P(B)=2*B^4+6*B^3+5*B^2+1.
```

If F!=0, apply the new transfer to this same integer F. The exact endpoint
test in `check_height.py` is

```
[2*(b*^2-6)]^(32*m) > (3*H+14)^(32*m) * P(b*)^577.
```

This suffices for every B>=b*, not just the checked endpoint. After
factoring powers of B, the relevant ratio is a positive constant times

```
B^(64*m-2308) * (1-6/B^2)^(32*m)
    / (2+6/B+5/B^2+B^(-4))^577.
```

For B>sqrt(6), its first factor strictly increases (64m-2308>0), its
second increases, and its positive denominator decreases. Thus the
endpoint inequality contradicts the transfer for all allowed B. It passes
at (E,m)=(2118,45) and (2010,47), so F=0. The root for b is finite and
nonidentity, hence b!=0. The same inherited Lucas statement then gives
log B>|a|-3, with its unchanged absolute-value/sign conventions.

## Scalar margin and final input contradiction

For order 45 at E=2118 retain the stronger old target h(beta)<c/4.
The exact integer test is c*^415>(4H)^992, since
1-alpha/31=415/992. The function c^(415/992) increases, so this controls
every c>=c*. For the optional order-47 route at E=2010 use instead

```
8^992 * c*^415 > (25*H)^992, hence h(beta)<8*c/25.
```

Both routes therefore satisfy the common weaker target h(beta)<8*c/25.
For n!=beta the same nonzero reduced numerator N has
|N|<=2*exp(h(beta))*B and radical order 12. Since K0<7H, retain the source
coarse transfer at this consumer, obtaining

```
log B < [12/(24-alpha)]*log(40H) + [alpha/(24-alpha)]*h(beta)
      = (384/191)*log(40H) + (577/191)*h(beta).
```

The source absorption remains valid: alpha/12<2 and
7H*2^(alpha/12)+6<40H. The exact comparisons 40H<2^670 and b*>67000 give
log(40H)<670<|a|/100. Also c<=|a|+1. Therefore

```
log B < (4712/4775)*|a| + 4616/4775 < |a|-3
```

for |a|>=301, another checked consequence of the anchor. This contradicts
the Lucas lower bound and forces n=beta integral. The final inference to
X integral is unchanged: outside 2 and 3 a negative valuation of X makes
the quadratic term of beta uniquely minimal, including the leading
coefficient valuation one at 17; 11016=2^3*3^4*17. At 2 and 3 the anchor
already supplies integrality. No extra prime is excluded.

E=2112 fails the displayed Lucas test at order 45; E=2004 fails the chosen
scalar test for order 47. These negative comparisons concern only the
stated sufficient estimates. No parameter or circuit optimum is asserted.

## Source comparison, outputs and review boundary

`check_height.py` compares both actual generated raw systems with #13's
systems: all coordinates, residuals, gates, values, guards, census and
anchor expressions agree. Only the fixed-parameter declaration and
descriptive variant metadata may differ. This is equality over the formal
parameter S, not equality after different numerical specializations.

The complete replay starts from the frozen builder, applies the same
scalar-chain, preparation-zero and cubic substitutions, compiles, checks
the source gates, omits the same two unused base slots, transports the
four factored conics and checks every diagonally scaled coefficient.
Counts include the input:

| Order | E | Variables | Residuals | Monomials | Exact maximum |
| --- | ---: | ---: | ---: | ---: | --- |
| 45 | 2118 | 380 | 349 | 26025 | 28902*3^1412 (679 digits, 2253 bits) |
| 47 | 2010 | 383 | 352 | 26043 | 28902*3^1340 (644 digits, 2139 bits) |

Both polynomials have degree four, content one, all variables active and
input fourth-power coefficient one. The diagonal maps fix the input and
are bijections over Q; nonzero primitive row factors preserve rational
zeros. EXPECTED.json binds deterministic full expansions generated by
replay. The source manifest binds the complete local proof, contract,
implementation and inherited sources; its digest is recorded separately.

Historical disposition: the projective argument and varying-anchor
equivalence were already in the supplied package; their application to
the current exponent and sharper final input inequality is submitted here.
Current manuscript incorporation remains pending. Source comparisons and
integer checks do not prove the inherited arithmetic theorem or constitute
non-author acceptance. An independent decision must bind this exact proof
and application contract. See HANDOFF.md for cumulative evidence and scope.
