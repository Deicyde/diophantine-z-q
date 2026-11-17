# Higher detector precision above the 383-variable construction

This research alternative starts at commit
`a1f9233049cc0f8aeb2a6ccd7e7b613cec3c1ec0` (#12). It retains the
order-31 scalar chain and preparation zero. The inherited arithmetic inputs
remain conditional. No current manuscript or acceptance register is changed.

## The existing logarithm has uniform relative precision 51

Keep exactly the existing polynomial `G12(w)=sum(a_j w^j,j=0..12)`, with
`a0=1`, `a1=-2/5` and `a_j/a_(j-1)=(4j-5)/(4j+1)`. Work at every place
of `K=Q(sqrt(2))` above `p` outside `{2,3,5,7,13,17}`, including inert
places, with rational normalization `v(p)=1`. These extensions are unramified,
so coefficient and local-element valuations are integral. The curve parameter
`D=11-6sqrt(2)` is a unit because its norm is 49.

For a nonidentity formal point with depth `r=v(z)>=1`, the actual recurrence
and invariant-differential identity in `quartic_v10.tex:9220–9258` give
`log_E(Q)=z G_infinity(w)`, `v(w)=4r`. The factorial-denominator argument
in that proof gives `v(a_j)>=-(4j+1)/(p-1)` independently of its original
large-prime cutoff. The earlier extension to the present exceptional set is
written in `proofs/prior/round5/geometry_round5.tex:68–95`; round six uses
a weaker bound of 45. We reapply the coefficient argument, rather than
applying the large-prime theorem with its hypothesis removed.

The reduced denominator of `a13` is

```
5^2 * 7 * 17 * 29 * 37 * 41 * 53.
```

Every admitted prime consequently has `v(a13)>=-1`. Its omitted term has
valuation at least `52r-1>=51r`. For `j>=14`, integrality of valuations and
`p>=11` give

```
v(a_j w^j) >= 4jr - floor((4j+1)/10) >= 51r.
```

For the last inequality it suffices to set `r=1`. At `j=14`,
`4j-51-floor((4j+1)/10)=0`; increasing j increases this expression by at
least three. These lower bounds tend to infinity, so they control the
whole infinite tail. Multiplication by z gives absolute error at least
`52r`; dividing by the logarithm, whose valuation is r, gives relative
error at least `51r`. The unchanged weak estimate is
`log_E(Q)/z(Q) in 1+p^(4r) O`.

The bound 52 is not uniformly available for this truncation. At the admitted
prime 53 and depth one, the j=13 term has valuation 51, whereas every j>=14
term has valuation at least `4j-floor((4j+1)/52)>=55`. Hence the tail has
valuation exactly 51. Formal parameters of depth one exist over the local
field; this observation concerns the uniform local lemma, not a claim that
every global constructed witness realizes that case.

The real polynomial and its positive lower bound `G12(1)>0` are unchanged.
There is no new denominator exclusion, point chart, logarithm coordinate or
exceptional prime. The input numerator still uses G2 with precision 12.

## Exact weight circuits for orders 46 and 47

Retain the positive chart, five-contact function F, positive square scale A,
`delta=98A lambda-1`, `q1=A(A delta)^4/F` and `E=q1 delta^2=1/R`.
Here E denotes the weight coordinate, not the integer anchor exponent below.
The previous circuit already stores

```
q12=E^11 q1^12,  mixedHigh=q12^2=E^22 q1^24.
```

For high order 46 insert `V=mixedHigh*delta` and replace the last weight by
`q46=V^2/q1`. Since `delta^2=E/q1`, this is `E^45 q1^46`.
For high order 47 instead insert `V=mixedHigh*E`, obtaining
`q47=V^2/q1=E^46 q1^47`. In both cases this is precisely
`q_m=e^(2m-1)/delta`, with `e=q1 delta`, as required by the contact-unit
normalization in `proofs/detector_round7.tex`.

All these quantities are strictly positive on the established source domain.
Each new equation is quadratic, and the new denominator q1 cannot vanish.
The equations uniquely extend an existing point to the stated weights;
conversely, they imply the stated weights on every solution. The extra
coordinate survives the full compiler once per detector. The existing
q1-square and q1-cube remain consumed by the order-one product evaluation.

Only three last-weight rows change and three lift rows are added after
identifying renamed high-order blocks. Every other raw residual and every
guard is unchanged. The fixed anchor value changes separately. All six
high tests receive order m: the primary inverse root, three long-log cross
tests, `L1-beta`, and the Lucas polynomial. The eight order-one tests and
the two order-12 tests keep their orders and their exact underlying values.

## Local soundness and the same objects downstream

The arbitrary-order one-place proof and its contact-unit normalization apply
to these exact positive weights. They produce every required test order at
one common place above each consumed contact prime. The primary inverse-root
test gives formal depth at least m. The other primary roots and alternate
inverse abscissae still put their respective points on the formal branches.

Read the actual two-anchor argument with present labels, as in
`quartic_v13.tex:19689–19706` and the small-prime adaptation in
`proofs/prior/round5/arithmetic_round5.tex:145–182`. Its full ratios are
`u_i/h` and `(u_i-n_i)/(h-1)`, with guarded h and h-1 nonzero. One denominator
is a p-unit, so one ratio is integral. Weak logarithm-unit estimates preserve
these valuations; the cross congruence first transfers integrality to the
other ratio. Integrality of the primary truncated ratio then forces its
numerator point to have depth at least the primary denominator depth m.
Consequently the primary relative errors have precision at least 4m.

The alternate denominator and the three Lucas numerators have precision at
least 51, hence at least m for m=46 or 47. Integral ratios turn these
relative errors into absolute errors. Multiplication by h and h-1 and
subtraction give the actual label congruences `L_i=n_i mod p^m` for the
three Lucas labels. For the input label the same argument uses G2 and its
order-12 cross test, giving precision 12.

If any primary numerator point U_i is the identity, the raw chart gives
`L_i=0` and its integer index is `u_i=0`. The alternate point is the negative
of the corresponding guarded nonidentity root, so its logarithm ratio is
defined. The cross test forces `v(L_i')>=k_i`, with `k_i=12` for the input
and `k_i=m` for a Lucas label. The unchanged unit estimate preserves this
valuation in `r_i'=-n_i/(h-1)`. Since h-1 is an integer, `v(n_i)>=k_i`,
which proves the desired congruence for `L_i=0`. This covers every primary
identity branch without forming `log(O)/z(O)`. At an inert prime conjugation
preserves the valuation, so nothing is lost.

Thus the same literal Lucas residual of the same integer labels is divisible
to order m by the same contact radicals. No theorem about a different ratio,
norm of the height product, or different limiting point is substituted. The
scalar norm, its odd-valuation argument, split-41 case and order-31 conclusion
are unchanged. Raising `L1-beta` to order m only strengthens the retained
order-12 input conclusion.

## Completeness with simultaneous real and finite conditions

Use #12's actual order of choices: finite scalar depths, near-identity H0,
then the actual shifted scalar point Q, its anchor divisibility, roots and
scales, the finite continuity modulus L0 and a real neighborhood. These are
fixed before invoking the separated contact-prime theorem. The scalar real
limit and the condition `0<42r N^2<17` are unchanged.

In the final CRT replace `Pi^44` by `Pi^(m-1)`:

```
h=0 mod Pi^(m-1) M_minus,
h=1 mod M_plus,
h=h0 mod L0.
```

The already checked gcds `gcd(Pi,M_plus L0)=1`,
`gcd(M_minus,M_plus)=1`, and `gcd(M_minus,L0)=16`, with `64|h0`, prove
compatibility for either new exponent. The resulting progression still has
residue and modulus divisible by the component-group order m0. Its positive
tail is dense in the same identity component and meets the fixed real
neighborhood. This produces an actual final H with primary formal depth m,
all scalar conditions and all real bounds, not a point substituted at a limit.

For each fixed detector order, the weight formula is unchanged in form.
At infinity `q_m=O(lambda^-1)`, so its product tends to one and its physical
pole input remains asymptotic to `1/(4*98^6*A^6*lambda)`, eventually in
(0,17). At p=2,3,17 the existing formula
`v(q_m)=nu+(10m-6)(v(A)+v(98))` still tends to infinity with the prescribed
denominator depth nu. At contacts delta is a unit and the successful test
factors are one modulo p; at the opposite place inverse factors have residue
zero or one by odd valuation. The reciprocal trace is a unit. Elsewhere the
same R has even valuation, and multiplication by its trace square preserves
the square-denominator conclusion. This checks the actual specialized pole
converse, including its zero branches, for the changed detector inputs.

## Anchor 2016 and all height consumers

Keep exactly `alpha=577/32` and
`H=3*2^106*(2^32*3^9)^6*46410^18+128`. The source height-transfer statement
is `B^2-6<7H |N|^(alpha/k)` for each nonzero consumed numerator N.

Change the fixed anchor to `3^2016`. The same even-anchor argument requires
`0!=a-1 in 2*3^1007 Z`; all parity and 2/3-integrality conclusions remain.
Completeness permits this finite condition alongside the scalar preparation.
Put `c*=2*3^1007`, `b*=3^1007`. Exact integer comparisons give

```
(c*)^415 > (4H)^992,
(b*)^(16m-577) > (24H)^(8m)  for every 46<=m<=51,
40H < 2^670,  b*>67000,  b*>152.
```

The first gives `h(beta)<|a-1|/4` from scalar order 31. For a nonzero
Lucas residual, the unchanged bound `|F|<5B^4`, with `alpha/m<1/2`, gives
`B^(2-4alpha/m)<7H*5^(alpha/m)+6<24H`. The second exact comparison
contradicts this for every `B>=|a|>=b*`, so the same Lucas theorem gives
`log B>|a|-3`. The unchanged order-12 input comparison and the remaining
displayed margins give the opposite bound when `n!=beta`, exactly as in
#11's final input consumer. Thus the conclusion about the actual input
coordinate is unchanged, conditional on the inherited inputs.

For these sufficient margins and exponents divisible by six, the preceding
anchor 2010 fails the scalar inequality. At 2016, order 45 fails the Lucas
inequality. These are boundaries of the displayed sufficient estimates,
not impossibility or optimality results for other proofs.

## Measured alternatives and review boundary

After the same certified free omission, four conic transports and input-fixed
diagonal scaling, both alternatives have 386 coordinates and 355 residuals.
Order 46 has 26,046 monomials; order 47 has 26,037. Both have exact maximum
coefficient `28902*3^1344`, with 646 decimal digits and 2146 bits. The original
#12 remains better in variable count: 383 variables with 682-digit coefficients.

The replay checks every gate and compiler operation, all outside raw consumers,
the conic transports, every scaled row and every polynomial coefficient.
Those finite checks do not prove the uniform arithmetic arguments above.
No cost-neutral higher-order weight circuit has been established here, and
no exhaustive circuit optimality claim is made.

Historical disposition: the recurrence, factorial bound, arbitrary-order
detector and simultaneous progression arguments were found in the cited
sources and read; this packet sharpens their numerical application and
checks the changed consumers. Manuscript disposition: pending. Independent
review and formal current-manuscript acceptance remain separate from these
author arguments and finite measurements.
