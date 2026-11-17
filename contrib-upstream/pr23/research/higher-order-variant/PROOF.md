# Higher orders: an optional 377-variable construction

This conditional non-release alternative starts above the uniform odd-power
detector packet, commit `32abb654ec295e28b51f92a51d7f12d4c5a626ec` (#19).
It retains that 376-variable construction as an alternative. One additional
scalar inverse coordinate raises scalar order31 to47. A different detector
chain of the same size raises detector order46 to50. Anchor exponent1512
then suffices, giving377 variables and327-digit coefficients after the
exact row reduction and diagonal map. New arithmetic applications are
proved below; earlier favorable reviews do not accept these changes.

## Actual source objects and scalar descent

Use K=Q(sqrt(2)), valuations v_p(p)=1, and the retained exceptional set
{2,3,5,7,13,17}. The scalar sources are the actual norm descent in
`scalar-chain-reduction/PROOF.md`, the preparation-zero application in
`scalar-preparation-zero/PROOF.md`, and the two-place proxy argument in
`conditional-quartic-reduction/proofs/prior/round5/geometry_round5.tex`,
sections “A scalar test using only a local approximation to the ratio”
and “A uniform two-place trace argument, including the prime41”.

Keep beta=2401+2754(2X+1)^2, r=beta(beta-1)(32beta+343)>0,
H=[h]P, Q=S-P=[a-1]P, and the same guarded nonidentity charts. Write

```
f(H)=A+B*sqrt(2), f(Q)=C+D0*sqrt(2),
Tproxy=Re(k_H*w_S), kappa=r^-15,
y=Tproxy/r^32,
J3=D0^2+kappa*y^2,
J2=C^2+kappa*J3^2,
J1=B^2+kappa*J2^2,
r*N=A^2+kappa*J1^2.
```

The existing inverse chain stores r^-1,r^-3,r^-7,r^-15. Add
rInverse31=(r^-15)^2/r and replace the proxy-leaf equation by
r*y=rInverse31*Tproxy. Keep kappa=r^-15 in every norm node. Since r>0,
the added inverse and all quotient extensions are unique and defined.
The source checker checks the actual defining polynomials, not names.

The retained chart implies A>0, hence N>0. The scalar physical pole input
is b_scalar=42rN^2, with preparation zero and positive conic coefficient
42r. The exact A/tri identities of #18 continue to apply to this N: in
particular rInverse*T=42N^2 defines T=b_scalar. Its conic normalization,
including the constant rescaling of Bh and every zero branch, remains
the one proved in that packet. N changes as a function of the outside
points; no bijection of arbitrary old and new scalar pole witnesses is
claimed. The inherited generated comment W>=1 is corrected to W=N>0.

At a consumed prime with odd R=v_p(r), the unchanged input-polynomial
argument gives R>0: a pole of X would give the even valuation6v_p(X).
The preparation-zero obstruction for this physical b_scalar gives
v_p(N)>-R/2. In N=A^2/r+r^-16*J1^2, the two coefficient valuations
-R,-16R have opposite parity. In each inner node they are0,-15R.
Thus no cancellation occurs between finite summands. Zero leaves use
valuation infinity. Successive strict lower bounds divided by R are

| Object | Bound |
| --- | ---: |
| A | 1/4 |
| J1 | 31/4 |
| B | 31/8 |
| J2 | 91/8 |
| C | 91/16 |
| J3 | 211/16 |
| D0 | 211/32 |
| y | 451/32 |
| Tproxy | **1475/32** |

The first four leaf bounds put the same H and Q in the formal group at
every place above p before invoking the proxy lemma. Its source permits
every positive scalar order. Specifically k_H/k_Q=((a-1)/h)u, where
u is1 modulo p^4 at both places. The exact recovered chart implies
w_S*k_Q=-h_P modulo p, including the nonunit fixed-coordinate place
above41: when h_P is nonunit, h_S is also nonunit and the congruence
still follows. The rational trace coefficient U0 of u*w_S*k_Q is
1 modulo p. Thus Tproxy=((a-1)/h)U0 and

```
v_p((a-1)/h)=v_p(Tproxy)>(1475/32)R>=46+3/32.
```

Integral valuations imply v_p(Tproxy)>=47; h is a nonzero integer, so
v_p(a-1)>=47. The unchanged shifted-point inverse guard excludes a=1.
For the same scalar contact radical M(beta), M(beta)^47 divides a-1.
This is radical order47, not a claim of order47R. No trace of a different
proxy and no new exclusion of41 is used.

## Scalar completeness with the actual shared H

Fix integer X, hence positive rational r and kappa. For every p dividing r,
write R=v_p(r)>=1. Require all five leaves A,B,C,D0,y to have depth
at least16R+1. The same node calculation gives each inner output depth
at least17R+2 and, at the root, v_p(N)>=16R+2. The new proxy condition is
v_p(Tproxy)>=48R+1. It is a finite condition, imposed after H is fixed.
At primes dividing42 and at17 where r is a unit, positive leaf depth
suffices, giving v_p(N)>=2. The proxy source proves that after fixing H,
taking Q deeper makes Tproxy/r^32 satisfy any prescribed finite depths,
including exceptional places; good reduction there is not assumed.

The unchanged exact integer congruences for rho=42r are
rho=4 mod32, rho=81 mod243 and rho=13 mod17. They make rho a local
square at2,3,17 with valuations2,4,0. Since N is nonzero, b_scalar has
the same squareclasses. The imposed depths give v2(b_scalar)>=3,
v3(b_scalar)>=1 and v17(b_scalar)>=2. On the support of rho its
denominator is integral; elsewhere its valuations are even. Its reduced
denominator is therefore a square.

For real smallness use the same real orbit closure G and identity
component G^0 as the preparation-zero proof. A progression with residue
and modulus divisible by m0=|G/G^0| has dense positive tail in G^0;
no density in the full product of real circles is assumed. Choose a
positive H0=[h0]P in a sufficiently divisible progression, including
64m0, with the finite H depths and near both real identities. Fix H0,
then take Q=[s]P near both identities in a progression satisfying all
new finite depths, 6|s and 3^755|s. Its nonzero indices can be arbitrarily
large. As Q tends to O, C,D0,y tend to zero, because r is fixed and
Tproxy tends to zero. Therefore

```
N -> (A^2+r^-15*B^4)/r,
b_scalar -> (42/r)*(A^2+r^-15*B^4)^2.
```

Choose H0 first to make this limit less than17/8, then an actual Q
to make b_scalar(H0,Q)<17/4. With Q fixed, continuity supplies a real
neighborhood of H0 where0<b_scalar<17 and a fixed modulus L0 preserving
all finite conditions. Fix the other labels, roots and positive scales;
shrink to a neighborhood with compact closure avoiding comparison poles.
All comparison bounds are now fixed before contact-prime selection.
The final H is selected below in this same neighborhood and congruence
class. It is not an independent second choice or a limiting point.
The specialized pole converse then supplies new scalar witnesses.

## Seven-coordinate order50 detector chain

For each of the three actual positive rational-square scales
A_det=1,C0^2,(C0+C1)^2, keep the parent's t=A_det*lambda,
delta=98t-1, five-contact product F, e=(A_det*delta)^5/F,
q1=e/delta>0 and R_det=1/(e*delta). The stored q1^2,q1^3 belong
to the order-one product. The new chain is

```
q4=(q1^2)^2, q8=q4^2, I=q1/q8=q1^-7,
q12=q8^2/I=q1^23,
h=q12^2=q1^46,
q50=h^2/I=q1^99,
q50^2, q50^3.
```

The actual builder shares q4 with the order-one product's fourth-power
coordinate; it does not allocate an additional copy. Two old coordinates
q1^6,q1^12 are replaced by q1^8,I. The seven-coordinate weight budget is
unchanged. All rows are quadratic. q8 and I are positive and nonzero,
so the quotient equations admit no new cleared-denominator branch.
The auxiliary I can grow at infinity; only the implemented positive
weights q1,q1^23,q1^99 enter the product, and these decay there.

There are exactly eight order-one tests, two order12 tests and six
order50 tests. Their underlying field functions and guards agree with
the parent under order renaming. The six high tests are g_H, three
Lucas-label cross comparisons, L1-beta and the literal Lucas polynomial.
The low tests continue to enforce every primary and alternate formal
domain needed below; none of the problematic dropped-test proposals is
used. The two input tests remain order12.

For m in{1,12,50}, apply the actual one-place proof to
d=D/delta^(2m-1). Then R_det*(d/R_det^m)^2=q1^(2m-1)D^2.
The five delta contact values are -1,1,24/25,-24/25,39/25, units
outside the retained exceptional set. Thus v(d)=v(D) at every consumed
contact. The common-place descent in #19 is uniform in the positive
integer m: for odd r_det=v_p(R_det), with l=max v(W), the pole
obstruction gives r_det>0,l>-r_det/2 and
v(d)>(m-3/4)r_det>=m-3/4. Integral valuations imply v(D)>=m
at one place for all sixteen tests simultaneously. Zero tests and both
split/inert cases are included. This reuses the proved small-prime
reapplication, not the old large-prime theorem with its cutoff deleted.

The actual product has W>=1 at both real embeddings. Its circuit computes
n=N_K(W)/(2W0) and B_pole=n^2/(e*delta)
=R_det/Tr(W^-1)^2. The factor two and actual trace are retained. W,
trace and private pole inputs change; R_det alone is unchanged.

## Precision50 and the literal consumers

The source is `detector-cube-reuse/references/precision51_PROOF.md`,
read together with its round-five two-anchor sources. The unchanged
degree12 logarithm has relative precision at least51 at every retained
prime. Its first omitted coefficient has denominator
5^2*7*17*29*37*41*53, hence loss at most1 there; its term has depth
at least52r-1>=51r. For j>=14, the entire tail is controlled by
4jr-floor((4j+1)/10)>=51r and these bounds tend to infinity.
This includes the sharp loss at53. We use only50, not a nonexistent
uniform precision52. The input logarithm G2 still has precision12.

For each root retain the exact ratios u_i/h and (u_i-n_i)/(h-1), with
guarded nonzero h,h-1. At least one integer denominator is a p-unit,
so one ratio is integral. Weak logarithm-unit estimates preserve its
valuation. The cross congruence transfers integrality to the other ratio
before relative errors are treated as absolute errors. The primary
denominator has depth at least50; integrality forces the nonidentity
primary numerator to have at least this depth. Its relative error is
therefore at least200. The alternate denominator and Lucas numerators
have relative precision51, sufficient for50. Multiplying by h and h-1
and subtracting gives L_i=n_i mod p^50 for each Lucas label.
The same argument uses order12 and G2 for the input label.

If a primary numerator is O, its chart value and index are L_i=u_i=0.
The alternate point is the negative of the guarded nonidentity root.
The cross test forces its truncated ratio to have valuation at least k_i
(12 for input,50 for Lucas). Its unit estimate preserves the valuation
of -n_i/(h-1); integer h-1 then gives v(n_i)>=k_i. This treats every
identity branch without dividing by a zero logarithm. Conjugation preserves
inert valuations. The literal integer Lucas residual thus receives order50
at all three contact radicals; the reduced input numerator still receives12.

## Simultaneous higher-order detector completeness

After the fixed data described above, strengthen the finite denominator
modulus, prime cutoff and real bound in the same separated prime theorem.
Merge repeated integral contact forms while preserving their incidence
data; scale one leaves at least two distinct forms. The theorem permits
each of these fixed choices. No constant depends on a subsequently
selected prime or final progression. Its gcd conclusions give
gcd(Pi,M_plus*L0)=1, gcd(M_minus,M_plus)=1 and gcd(M_minus,L0)=16.
With64|h0 the system

```
h=0 mod Pi^49*M_minus,
h=1 mod M_plus,
h=h0 mod L0
```

is compatible. Its progression has residue and modulus divisible by m0.
Its dense positive tail meets the fixed neighborhood. This actual H
has primary depth50 and all the scalar finite and real properties.

At a selected contact v_p(R_det)=1 and delta is a unit; successful
tests of depth m make each factor1 modulo p. At the opposite place
odd valuations make every inverse factor have residue0 or1. The
reciprocal trace has residue1 or2 and is a unit. Away from the selected
contacts R_det has even valuation and its rational trace square preserves
parity. The same Gaussian congruences give squareclasses at2,3,17.
At real infinity q_m=O(lambda^(-(2m-1))); fixed bounded tests imply
W tends to1 and B_pole~1/(4*98^6*A_det^6*lambda), eventually in(0,17).
At p=2,3,17 put s=v_p(A_det)+v_p(98), nu=v_p(v) for the source
denominator v. The same leading terms give

```
v_p(q_m)=(2m-1)*(nu+4s),
v_p(B_pole)=nu-6s-2v_p(2)
```

once nu is large enough. All nu slopes are positive, including m50.
Choose nu to make products close enough to1, trace close enough to2
also at ramified2, and pole depths at least3,1,2 at2,3,17. These are
finite requirements fixed before prime selection. The specialized converse
supplies new private pole witnesses. Four factored conics keep their
positive coefficients and all zero branches.

## Anchor1512 and all height margins

The uniform even-anchor equivalence in
`proofs/optional_anchor_height_round7.tex`, with round-eight's noncircular
odd-label derivation, applies at E=1512. It gives all four labels odd,
X integral at2 and3, and0!=a-1 in2*3^755 Z. For completeness reevaluate
the private packed anchor value and choose its conic witnesses at this
new fixed parameter; no old witness-tuple equivalence is asserted.
The source equivalence covers both signs and zero packed summands.

Retain alpha=577/32 and Hheight=3*2^106*(2^32*3^9)^6*46410^18+128.
The scalar beta avoids0,1,2401,-343/32: equality2401 would require
X=-1/2, excluded by anchor2-integrality. The same height theorem on
the actual M(beta)^47 divisibility gives h(beta)<=Hheight*c^(577/1504),
c=|a-1|. Set c*=2*3^755 and b*=c*-1. Exact integer checks give

```
8^1504*c*^927 > (25*Hheight)^1504,
[2*(b*^2-6)]^1600 > (3*Hheight+14)^1600*P(b*)^577,
P(b)=2b^4+6b^3+5b^2+1,
40*Hheight<2^670, b*>67000, b*>=301.
```

The scalar inequality implies h(beta)<8c/25 for every c>=c*. For a
nonzero literal Lucas residual, the actual projective transfer in the
height-consumer packet gives Bmax^2-6<((3Hheight+14)/2)|F_Lucas|^(577/1600),
where Bmax is the largest absolute root label, not a pole input.
Its triangle bound is P(Bmax). The endpoint contradiction holds for every
Bmax>=b*: after factoring powers the ratio is proportional to

```
Bmax^892*(1-6/Bmax^2)^1600 /
       (2+6/Bmax+5/Bmax^2+Bmax^-4)^577.
```

The numerator increases and positive denominator decreases for Bmax>sqrt(6).
Thus F_Lucas=0, and the inherited Lucas theorem gives log Bmax>|a|-3.
For n!=beta the same nonzero reduced numerator has radical order12
and absolute value at most2*exp(h(beta))*Bmax. The unchanged final-input
consumer gives

```
log Bmax < (384/191)*log(40Hheight)+(577/191)*h(beta)
         < (4712/4775)*|a|+4616/4775 < |a|-3,
```

using c<=|a|+1 and the displayed thresholds. Contradiction forces beta=n
integral. Outside2,3 a negative valuation of X makes its quadratic term
uniquely minimal, including the coefficient valuation1 at17; at2,3 the
anchor supplies integrality. Hence the conditional input conclusion is
unchanged. No minimal anchor or universal circuit optimum is asserted.

## Finite representation and scope

The portable generator compares the actual parent and new raw systems,
canonicalizing high-order names and the shared fourth-power coordinate.
It checks every outside row, field expression, guard and gate; changed
rows are checked against their actual quotient identities. Seven negative
controls and exact scalar/local/height calculations accompany it. The
complete compiler, gate checker, four conic transports and independent
diagonal checker produce377 active variables,346 quadratic residuals,
25979 quartic monomials, content1, input fourth-power coefficient1,
and maximum327 digits/1084 bits. Every coefficient is compared.

The supplied fixed diagonal map has nonzero rational2/3-power entries
and fixes the input. Primitive row normalization and summing squares
preserve rational zeros. EXPECTED.json binds the complete generated
decimal table; no committed full expansion or floating-point optimality
certificate is claimed. The original Opus weight47/scalarpoles/compose
notes and corrections remain verbatim in #18's prior-investigation archive.
This packet proves the present applications, retaining all earlier limits.
New non-author review is required. Full published-source/global closure,
current-manuscript incorporation and designated App acceptance remain
separate from this conditional local research contribution.
