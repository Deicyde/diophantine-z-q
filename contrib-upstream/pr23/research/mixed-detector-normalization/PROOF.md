# Mix two existing detector normalizations: 380 variables, 644 digits

Parent: the height-consumer PR #16 at
`59c59e5589d86036ee41994c82a2b900fce85c2d`. This layer keeps the default
380-coordinate budget and reaches its optional 644-digit coefficient
regime. Six tests have order 46 instead of 45, and the anchor exponent is
2010 instead of 2118. The small-coefficient target needs order 46; no
order-47 conclusion is asserted for the new detector.

The change combines two already documented normalizations. The frozen
package's `proofs/prior/round5/arithmetic_round5.tex`, “Choose the detector
coordinate and guard together”, uses e^(2m-1)/delta^3 for all tests.
`proofs/detector_round7.tex` changes all weights to e^(2m-1)/delta.
Here only the high tests use the older normalization. No new prime, point,
logarithm, height theorem or global arithmetic assumption is introduced.
The inherited global qualifications remain; this is a new local argument,
not a projection equivalence between arbitrary old and new pole witnesses.

## Actual circuit and exact weights

Retain the three positive rational-square scales A=1,C0^2,(C0+C1)^2 and

```
t=A*lambda, delta=98*t-1,
F=t*(t-1/49)*(t-1/50)*(t-1/2450)*(t-32/1225),
e=(A*delta)^5/F, R=F/(A^5*delta^6), E=1/R=e*delta.
```

The source positive chart gives t>=32/1225 and delta>=39/25. The unchanged
equation q1*F=A*(A*delta)^4 has strictly positive right side, excludes
F=0, and implies F,q1,E>0. These are actual guards, not extra assumptions.

The inherited cubic reuse computes

```
q1=e/delta,
e3=q1^3*delta^3, e6=e3^2, e12=e6^2,
q12=e12^2/E=e^23/delta, h=q12^2=e^46/delta^2.
```

The cube delta^3 is the same affine expression in existing contact-polynomial
coordinates. The old last gate is q1^3*q45=h^2. Replace it with

```
q1*qHigh=h^2, hence qHigh=e^91/delta^3.
```

The denominator is the already stored positive q1. Both equations are
quadratic in stored coordinates; no new coordinate, product or denominator
guard is needed. The old q1 cube stays because the low-order products and
e3 still consume it. Compared with the parent's optional order-47 circuit,
this omits each `highLift=h*E` coordinate. It does not claim the same weight
or the same private detector pole input as that optional circuit.

The eight order-one tests keep q1, and the two order-12 tests keep q12.
The six high tests receive qHigh: the primary inverse root g_H, three
Lucas-label cross tests, L1-beta and the literal Lucas polynomial. Their
underlying field functions, all point charts and all logarithms are
unchanged. The checker compares every outside row and guard after matching
the order labels; only the three final high-weight defining rows change.
The anchor specialization is tracked separately.

## One common place, with the precise normalized inputs

At a consumed prime p outside S={2,3,5,7,13,17}, the contact map
phi(t)=-49+1/t has finite contact at exactly one of the five t values.
Their delta values are -1,1,24/25,-24/25,39/25, all p-units. A pole of t
maps to -49, distinct from the target contacts modulo these primes.
The actual radical and unit checks are in round five. Because A is a
rational square, 5*v_p(A) is even, so an odd contact gives odd v_p(R).
The small-prime reapplication in `proofs/prior/round4/arithmetic_round4.tex`,
“Use the finite exceptional set actually needed”, supplies the pole
implication outside {2,3,17}. The proof of the one-place lemma uses only
that implication, unramifiedness of K and integral normalized valuations;
it does not require a large prime. All consumed primes are at least 11.

Apply that actual proof with order m and normalized field input d as follows:

| Tests | m | d supplied to the one-place lemma |
| --- | ---: | --- |
| Eight low tests | 1 | D/delta |
| Two input tests | 12 | D/delta^12 |
| Six high tests | 46 | D/delta^47 |

For the first two rows, 1+R*(d/R^m)^2=1+(e^(2m-1)/delta)*D^2.
For the last, it is 1+(e^91/delta^3)*D^2. These identities follow from
R=1/(e*delta) with no omitted unit factor. The lemma permits arbitrary
field inputs and different orders; it requires no a priori integrality
of d. Thus mixed normalizations are legitimate within one product W.
Since delta is a unit at every consumed place, v(d)=v(D) there.

For completeness of this application, write r=v_p(R), an odd integer.
For every nonzero d the nonconstant term has odd valuation
r+2(v(d)-m*r), so the corresponding factor has valuation its minimum
with zero. Consequently each v(W)<=0. At a place attaining
l=max(v(W)), trace integrality gives v_p(Tr(W^-1))>=-l. The certified pole
input Bpole=R/Tr(W^-1)^2 therefore has odd valuation at most r+2l.
The pole implication excludes a negative odd valuation, so r>0 and
l>-r/2. At that same place every factor has valuation at least l. For
each nonzero d this implies v(d)>(m-3/4)*r>=m-3/4, hence v(d)>=m.
Zero tests satisfy the conclusion directly. This is one common place for
all sixteen tests, at split and inert primes. No identity-point division
or inverse-limit/index-set change is involved.

The actual product is still W=product(1+q*D^2), with the assigned weights.
They are positive rationals, so W is at least one at both real embeddings.
Thus W0>=1, N(W)>0 and Tr(W^-1)>0. The circuit uses exactly

```
n=N(W)/(2*W0),  Bpole=n^2/E=R/Tr(W^-1)^2.
```

Every denominator is nonzero. This is the same R required by the lemma,
although W, its trace and the pole input have changed. The four factored
pole transports retain their positive-input hypotheses and zero branches.

## Actual logarithm and height consumers

The supplying precision proof is preserved verbatim at
`detector-cube-reuse/references/precision51_PROOF.md`. It proves relative
precision at least 51 for the existing G12 at every retained prime and
explicitly treats orders 46 and 47. Its tail covers every j>=13, including
the denominator loss at p=53; no order-52 assertion is used. G2 still
supplies the input order 12, and the weak primary error has precision 4r.

Here the high primary test gives depth at least 46. Apply the same actual
two-anchor comparison to u_i/h and (u_i-n_i)/(h-1), with the source's
guarded h,h-1. One denominator is a p-unit; integrality transfers through
the cross test before relative errors are treated as absolute errors.
The primary error has precision at least 184, and the alternate error
has precision at least 51. Thus the three Lucas labels agree modulo p^46.
The input comparison retains order 12. For U_i=O, L_i=0 and u_i=0;
the alternate root is nonidentity, and its cross test gives the desired
divisibility of n_i without forming log(O)/z(O). Conjugation preserves
valuation at inert primes. These are the same objects and branches as
the supplying proof, with m=46.

Consequently the same literal Lucas integer F has the same three radical
divisibilities to order 46. The order-31 scalar chain is unchanged. Use
the parent's sharper projective transfer with alpha=577/32,
H=3*2^106*(2^32*3^9)^6*46410^18+128 and K0=(3H+14)/2. At E=2010 set
c*=2*3^1004 and b*=c*-1. Exact integer tests give

```
8^992*c*^415 > (25*H)^992,
[2*(b*^2-6)]^(32*46) > (3*H+14)^(32*46)*P(b*)^577,
40*H<2^670, b*>67000, b*>=301,
P(B)=2*B^4+6*B^3+5*B^2+1.
```

The parent's uniform endpoint proof now has positive exponent
64*46-2308=636. It therefore gives F=0 and the same Lucas lower bound.
The scalar inequality gives h(beta)<8|a-1|/25; the exact order-12 input
inequality gives log B<(4712/4775)|a|+4616/4775<|a|-3. Thus n=beta and
the unchanged 2/3-integrality and leading-coefficient argument give X
integral. The new detector's proven order 46 is sufficient for every
consumer; an order-47 conclusion has not been borrowed from the parent.

## Simultaneous completeness and all pole hypotheses

Use the parent's optional order-47 completeness choices at E=2010.
They already supply the same input, scalar preparation-zero block, root
points, fixed positive-square scales, real neighborhood, finite continuity
modulus and actual final H. The primary progression Pi^46 gives depth at
least 47, hence more than the new required 46. Alternate points still need
only depth one. All sixteen underlying field tests are the same. Their
real bounds and common finite lower valuation bounds are fixed before the
prime-selection theorem chooses its arbitrarily large real and finite
parameters. No old pole witnesses are presumed valid for the new W.

At a selected contact prime, v_p(R)=1 and delta is a unit. At the successful
place each new high factor has nonconstant valuation at least
1-2*46+2*46=1 (in fact the old depth-47 witnesses allow a stronger margin).
The unchanged low factors also equal one modulo p. At either place every
nonzero nonconstant term has odd valuation, so each inverse factor has
residue zero or one. Thus the reciprocal trace has residue one or two and
is a unit. The new Bpole has positive contact valuation. At every other
prime the unchanged contact-product formula for R gives even valuation;
Bpole differs from R by a rational square. Its reduced denominator is
therefore a square. In particular primes where delta vanishes away from
the contacts cause no new obstruction. The fixed Gaussian classes still
make R, and thus Bpole, squares in Q2,Q3,Q17.

For fixed A and lambda tending to positive infinity, e tends to 98^5*A^5,
while delta is asymptotic to 98*A*lambda. The low weights are O(lambda^-1)
and the new high weight is O(lambda^-3). Uniformly bounded tests give
W=1+O(lambda^-1), Tr(W^-1)=2+O(lambda^-1), and

```
Bpole ~ 1/(4*98^6*A^6*lambda).
```

Hence 0<Bpole<17 for a sufficiently large prescribed real parameter.
The earlier rejected stronger normalization caused growth at infinity;
this mixed choice instead improves decay of the high factors.

At p=2,3,17 use the source's denominator v=D0^2*w^2, numerator u a selected
prime, nu=v_p(v), eta=v_p(A), alpha_p=v_p(98), and s=eta+alpha_p.
For sufficiently large prescribed nu the same leading-term computation
gives v_p(delta)=s-nu and v_p(e)=5s. Thus

```
v_p(q1)=nu+4s,
v_p(q12)=nu+114s,
v_p(qHigh)=3nu+452s.
```

Each tends to positive infinity as nu grows, even if the fixed s is
negative. The fixed neighborhood bounds on the tests then make the trace
as close to two as needed, including above the ramified prime two.
The unchanged v_p(R)=nu-6s yields
v_p(Bpole)=nu-6s-2*v_p(2). Prescribe nu large enough for the same local
pole bounds v2(Bpole)>=3, v3(Bpole)>=1, v17(Bpole)>=2 and all factor bounds
simultaneously. These are additional finite lower bounds on already freely
chosen parameters, not a new prime-pattern hypothesis. Together with the
real bound, squareclasses and square denominator, the same preparation-zero
pole converse supplies new private witnesses. Apply the existing four
factored-conic transports, including their zero cases. Scalar and anchor
witnesses retain the parent's meanings and E=2010.

## Computational and review boundary

The full compiled result has 380 variables including the input, 349
quadratic residuals and 26025 quartic monomials. Its maximum coefficient
is 28902*3^1340, with 644 digits and 2139 bits. It has degree four,
content one, every variable active and input fourth-power coefficient one.
The input-fixed diagonal map and nonzero row factors preserve rational
zeros. The runner checks the exact source differences, weight identities,
local exponent formulas, numerical consumers, all compiler gates, four
conic transports and every coefficient. EXPECTED.json binds the full
deterministic decimal expansion generated by replay.

Those finite checks do not prove the inherited arithmetic theorem or the
uniform existence arguments. A separately authored decision must bind the
new proof, nine-obligation contract and sources. The earlier round-five and
round-seven normalizations are prior justification; their mixed use at the
new order and consumers is the application reviewed here. Earlier negative
searches assumed more restricted weight families and did not prove
optimality. Current manuscript incorporation and full published-source
closure remain pending. See HANDOFF.md for attribution, findings and scope.
