# Uniform odd-power detector normalization

This conditional local construction starts above the scalar row
reduction of #18 at `ce15e8ece219a2bb000075a5a79f6ffd9bea6dfd`. It retains the 379-variable parent's scalar order31,
anchor3^2010, row rewrites and exact arithmetic objects. Changing the weight
chain saves one coordinate in each of the three detectors, giving 376
variables and coefficients of at most425 decimal digits. This is a changed
arithmetic application, not an equivalence of arbitrary pole witnesses.

## Exact source circuit and test interface

The supplying sources are the original one-place proof
`manuscripts/quartic_v10.tex`, lemma `lem:v5-one-place`, the actual small-prime
reapplication in round-four arithmetic, the normalization and completeness
arguments of rounds five/seven, and #17's mixed application. The source
statement's old p>76176 hypothesis is not silently removed: its proof uses
only the pole obstruction outside {2,3,17}, unramifiedness and integral
normalized valuations. Those inputs hold on the actual retained set
p outside {2,3,5,7,13,17}, by the same reapplication checked in #17.

Use K=Q(rho), rho^2=2, with v(p)=1. For each of the three positive rational
square scales A=1,C0^2,(C0+C1)^2, keep

```
t=A*lambda, delta=98*t-1,
F=t*(t-1/49)*(t-1/50)*(t-1/2450)*(t-32/1225),
e=(A*delta)^5/F, q1=e/delta, E=e*delta=1/R,
R=F/(A^5*delta^6).
```

The exact source chart and q1 defining equation imply F,delta,q1,E>0.
In particular the following quotients are defined on every allowed source
solution; no isolated cleared zero branch is being introduced.
The existing order-one product already stores q1^2 and q1^3. Replace
three old e^3,e^6,e^12 coordinates by two coordinates q1^6,q1^12 and set

```
q12=(q1^12)^2/q1=q1^23,
h=q12^2=q1^46,
q46=h^2/q1=q1^91.
```

Retain q46^2 and q46^3. These are seven new weight coordinates per
detector, versus eight in the parent. All rows are quadratic and every
denominator is the positive q1. The checker decodes the actual gates,
including their powers and consumers; no unstored product is counted free.
The old affine delta^3 expression remains an alias, not an extra coordinate.

The complete test interface remains eight order-one tests, two order12
tests and six order46 tests. The latter are g_H, the three Lucas-label
cross comparisons, L1-beta and the literal field Lucas polynomial. The
order12 tests are the input primary inverse root and input cross comparison.
The low tests retain the remaining three primary inverse roots and five
conjugated alternate inverse abscissae. All sixteen field functions,
point charts, logarithms, symmetric product identities, inverse guards and
scalar/anchor equations are unchanged. Their formal expressions agree;
their evaluated product W changes because q12 and q46 have new meanings.

## One common place for the actual normalized tests

For an order m in {1,12,46}, supply d=D/delta^(2m-1) to the one-place
argument. Direct calculation with R=1/(e*delta) gives

```
R*(d/R^m)^2 = (e/delta)^(2m-1)*D^2 = q1^(2m-1)*D^2.
```

Thus the implemented factors are exactly the source factors for these
normalized field elements. At every consumed odd contact, the unchanged
map phi(t)=-49+1/t puts t at one of the five finite contacts. Their delta
values are -1,1,24/25,-24/25,39/25, units outside the retained exceptional
set. A pole of t maps to -49, distinct from all target contacts there.
The rational-square scale contributes an even valuation correction, so
v_p(R) is odd as needed. Normalization preserves v(d)=v(D) at every
consumed place. The source proof permits arbitrary field elements d and
different positive orders; it assumes no prior integrality of these d.

Here is the application at a single common place. Put r=v_p(R), odd.
For nonzero d, the nonconstant term has odd valuation
r+2(v(d)-m*r). The factor valuation is its minimum with zero, so v(W)<=0
at each place above p. Let l=max v(W). Trace integrality gives
v_p(Tr(W^-1))>=-l. The pole certificate for B=R/Tr(W^-1)^2 excludes
negative odd valuation, and therefore

```
0<v_p(B)<=r+2*l,   r>0,   l>-r/2.
```

At a place attaining l, every factor valuation is at least l, since each
factor valuation is nonpositive. It follows that
v(d)>(m-3/4)*r>=m-3/4. Unramified integral valuations give v(D)=v(d)>=m.
Zero tests satisfy this directly. The same chosen place works for every
one of the sixteen tests, at split and inert primes.

The actual circuit computes n=N_K(W)/(2W0) and B=n^2/E. Every weight is
positive, so W>=1 at both real embeddings, W0>=1, N_K(W)>0 and its
reciprocal trace is nonzero. Consequently

```
B=n^2/E=R/Tr(W^-1)^2.
```

This is the source's exact consumed object, with the trace's factor two
included. Only R is unchanged. W, its trace, B and the private pole witnesses
are generally different from the parent. The earlier exploratory assertion
that all of them were unchanged is corrected, not adopted as a proof.

## The unchanged order46 consumers

The precision51 proof and #17's actual two-anchor application remain the
suppliers. At a primary depth at least46, the weak primary relative error
is at least184. Alternate G12 has relative precision at least51 at every
retained prime, including the denominator loss at53. G2 still supplies
input precision12. No logarithm polynomial or coefficient is changed.

At the exact ratios u_i/h and (u_i-n_i)/(h-1), one integer denominator
is a p-unit. The low formal-domain tests and cross congruence first transfer
integrality; only then are relative errors used as absolute errors. For a
primary identity U_i=O, L_i=u_i=0 and the alternate ratio is
-n_i/(h-1); its cross test yields the same required label divisibility
without dividing by an identity logarithm. Conjugation preserves inert-place
valuation. Thus the literal Lucas integer gets order46 and the reduced
input numerator gets order12 at exactly their prior consumers.

Scalar order31 and the actual proxy Re(k_H*w_S), including its two-place41
argument, remain untouched. With alpha=577/32,
H=3*2^106*(2^32*3^9)^6*46410^18+128, c*=2*3^1004 and b*=c*-1,
the same exact inequalities hold:

```
8^992*c*^415 > (25H)^992,
[2(b*^2-6)]^1472 > (3H+14)^1472*(2b*^4+6b*^3+5b*^2+1)^577,
40H<2^670, b*>67000, b*>=301.
```

The parent's increasing Lucas endpoint ratio has exponent636. Its scalar
bound h(beta)<8|a-1|/25 and exact final-input inequality
log B<(4712/4775)|a|+4616/4775<|a|-3 close the same soundness argument.
Here B in the height comparison is the maximum absolute root label, not
the private detector pole input. The unchanged anchor supplies the required
oddness and 2/3-integrality, and the final beta argument supplies input
integrality elsewhere. No new exceptional prime or domain is introduced.

## Simultaneous completeness for the changed pole inputs

Reuse the parent's method and choice order, not an arbitrary old tuple of
pole witnesses. Fix integer input and scalar finite depths, choose a real
near-identity H0, then the shifted scalar point and anchor divisibility,
root labels/points, positive scales, finite continuity modulus L0 and a
compact real neighborhood avoiding comparison poles. The root tests and
all real/finite bounds on D are fixed before contact-prime selection.
The unchanged scalar preparation-zero construction ensures its physical
input lies in (0,17) throughout that neighborhood.

The source prime-pattern argument permits an arbitrary fixed denominator
modulus, prime cutoff and real lower bound after these data are fixed.
Strengthen those fixed bounds to handle the three new detector products.
Repeated contact forms are merged with their incidence data retained;
scale one supplies at least two distinct forms. The unchanged gcd conditions
make the primary progression Pi^46*M_minus, the alternate progression
M_plus and h=h0 mod L0 compatible. Using the parent's depth47 choice is
more than sufficient for order46. Its positive tail meets the fixed real
neighborhood, producing an actual final H with every scalar and detector
condition simultaneously. The new prime choices need not reproduce the
old final H; no claim about an unchanged witness tuple is made.

At a selected contact, v_p(R)=1 and delta is a unit, so
v(q1^(2m-1))=-(2m-1). Successful tests have v(D)>=m, making the
nonconstant factor divisible by p. At the other place every nonzero
nonconstant term has odd valuation; each inverse factor has residue zero
or one. The reciprocal trace has residue one or two and is a unit, so
the new pole input has the required positive contact valuation. Zero tests
cause no exception. Away from the selected contacts, the same product
formula for R has even valuations, including zeros of delta away from the
contacts; the rational trace square preserves parity. The reduced pole
input denominator is a square. The fixed Gaussian congruences preserve
its Q2,Q3,Q17 squareclasses.

At real infinity with fixed A, q1=O(lambda^-1), hence the new order-m
weight is O(lambda^-(2m-1)). Uniformly bounded tests give W=1+O(lambda^-1)
and reciprocal trace tending to two. The actual pole input still satisfies

```
B ~ 1/(4*98^6*A^6*lambda),
```

and eventually belongs to (0,17). At p=2,3,17 put
s=v_p(A)+v_p(98), nu=v_p(v), for the source denominator v=D0^2*w^2.
For sufficiently large prescribed nu, the same leading-term computation
gives v(delta)=s-nu, v(e)=5s and

```
v(q_m)=(2m-1)*(nu+4s).
```

Every nu slope is positive, regardless of the sign of fixed s. Fixed
lower bounds on test valuations therefore make every factor tend to one
p-adically. Make the trace sufficiently close to two, including above the
ramified prime2, to obtain v_p(B)=nu-6s-2v_p(2). Choose nu large enough
for v2(B)>=3, v3(B)>=1 and v17(B)>=2 simultaneously with all other finite
bounds. This changes only freely prescribed finite constants, not the
prime-pattern hypothesis. The specialized pole converse now supplies new
private witnesses. Its factored-conic maps retain every zero branch and
positive coefficient. The scalar witnesses and anchor retain their parent's
meaning, and the earlier A/tri transport remains valid on this domain.

## Representation, evidence and review

The three source-chain replacements remove three coordinates after the
complete compiler and four conic transports. A fixed input-preserving
2/3-power diagonal map, checked against every normalized row and every
coefficient, gives 376 active variables,345 rows,25964 monomials
and425-digit coefficients. The final measured expectation is recorded in
EXPECTED.json; the complete table is generated, not committed.

The short chain and uniform odd-power normalization were contributed by the
Opus frontier exploration. Their original source, corrections, the later
order48/50 chains and restricted negative searches remain in #18's archive.
No historical priority or universal gate optimum is claimed. Source checks
and integer tests establish finite properties only. A new application
contract and non-author review must bind this proof, sources and consumers.
No earlier acceptance is silently transferred; global arithmetic and
current-manuscript integration remain conditional/separate.
