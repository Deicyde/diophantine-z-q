# Common-strict coordinate comparison and normalization defect

Integrated from the preserved [received derivation](inputs/MATHEMATICS.md).
Current execution and review status are in [VERIFICATION.md](VERIFICATION.md);
this ordinary proof does not by itself establish Lean compilation or its
arithmetic application. The four Lean sources are the formal authorities.

## 1. Exact input

Let R be a DVR, L its fraction field, m >= 0 and n=m+2. The matrix theorem
itself only needs a field L; the integral structure is used for the unit
criterion and for interpreting the retained determinant bases.

Take D0 in Mat(n,m;R), AF,AS in Mat(n,2;R), and

    DF=[D0 | AF],  DS=[D0 | AS].

The corresponding degree-(1,2) complexes share the actual strict subcomplex
[R^m -> R^n]. Its cohomology need not be torsion-free. The quotient on each
side is its actual local plane in degree one.

Let J be an integral local isomorphism, delta=det J in R^units. Retain the
actual cycles and closed rows:

    zF=(hF,v),   zS=(hS,Jv),
    DF zF=DS zS=0,
    lambdaF DF=lambdaS DS=0.

The functionals may be L-valued, including ones with a fixed clearing factor.
They are not independently replaced by primitive rows. Choose a fractional
complement x with eta=det[v,x] != 0 and set

    a=AF x, b=AS Jx, T=[D0 | a | b], theta=det T != 0,
    qF=lambdaF(b), qS=lambdaS(a).

The invertibility of T retains generic independence of the two boundary
lines in the strict H2 quotient. Its arithmetic justification is separate.
The source's axes-kernel statement, together with the requisite generic
strict cohomology identification, can supply it; it is not supplied by local
J alone. Neither eta nor theta is assumed to be an integral unit.

## 2. Coordinate definition

Use the explicit cofactor convention

    z lambda = u adj(D).

The normal-frame calculation below forces rank(D)=n-1. Thus adj(D) != 0,
and this specifies u uniquely. In degree-(1,2) rank-one cohomology this is
the ordinary inverse-determinant coordinate, with a consistent ordered-basis
orientation. The Lean development formalizes this cofactor specification and
its transformation; it does not build a derived determinant functor.

## 3. One normal form on both sides

Put

    BF=[e1,...,em,zF,(0,x)],
    BS=[e1,...,em,zS,(0,Jx)].

These are upper block-triangular matrices, so

    det BF=eta,   det BS=delta*eta.

Use different orderings of the SAME two target complement directions:

    TF=[D0 | b | a],  TS=[D0 | a | b].

Then det TF=-theta and det TS=theta. The actual cycle equations give

    DF BF=TF N,   DS BS=TS N,
    N=diag(I_m,0,1).

This is not a map from CF to CS. It is a separate change of frame in each
complex. Both actual classes become the coordinate vector e_(m+1).
Closedness, not a normalization guess, gives

    lambdaF TF=qF e_(m+1)^*,
    lambdaS TS=qS e_(m+1)^*.

The sole nonzero entry of adj(N) is 1 in position (m+1,m+1). Thus the two
normal-frame cofactor coordinates are qF and qS.

For D B=T N and invertible B,T, adjugate multiplicativity proves that the
old coordinate is det(B)/det(T) times the new one. Consequently

    uF=-eta*qF/theta,
    uS=delta*eta*qS/theta.                                  (1)

The common theta is retained throughout. In particular no nonunit strict
minor has been removed as if it were an integral unit. A nonprimitive local
class is also allowed: BF and BS need only be invertible over L.

## 4. Exact defect and integral-unit criterion

The determinant comparison from the common strict factor and J multiplies
retained line coordinates by delta. For qS != 0,

    delta*uF/uS = -qF/qS.                                 (2)

The stronger division-free identity is

    qS*(delta*uF)+qF*uS=0.                                (3)

For a subring R of L, define

    UnitRelated_R(a,b) iff exists epsilon in R^units,
                            a=epsilon*b.

This definition includes UnitRelated_R(0,0); it is false if exactly one
argument is zero. Calling every nonzero element a unit in L would lose the
arithmetic content and is NOT the definition used here.

Let c=delta*eta/theta != 0. Formula (1) gives

    delta*uF = c*(-qF),  uS=c*qS.

Multiplication by a common nonzero c preserves UnitRelated, even if c is
not an R-unit. Since -1 is an R-unit,

    UnitRelated_R(delta*uF,uS) iff UnitRelated_R(qF,qS).    (4)

When delta is the image of an actual integral unit, this also gives

    UnitRelated_R(uF,uS) iff UnitRelated_R(qF,qS).          (5)

For a DVR, this means equality of valuations, with the usual +infinity
convention at zero. The Lean development also supplies a consumer for a
multiplicative valuation trivial on images of R-units. It does not define
an additive valuation on arbitrary complexes.

## 5. Full boundary--cup adapter

Work in the source's compatible local bases, where J^2=1, and let

    beta(f,s)=epsilon*omega(f,Js),
    omega(f,g)=det[f,g].

Do not assume qF=qS. Instead require the full two boundary--cup identities
on the actual rows, for all local vectors s,f:

    lambdaF(AS s)=cF*beta(v,s),
    lambdaS(AF f)=-cS*beta(f,Jv).                          (6)

These are the presentation-level shadows of the actual maps through the
strict H2 quotient into the two degree-two cohomology spaces. They must be
proved from the retained arithmetic duality diagram to apply the adapter.
They are inputs here, not assertions about the manuscript already verified.

Evaluate at s=Jx and f=x. Involutivity and alternation give

    qF=cF*epsilon*eta,
    qS=cS*epsilon*eta.                                    (7)

For epsilon,cS != 0, (2) becomes

    delta*uF/uS = -cF/cS.                                 (8)

This identifies the exact normalization defect. If cF=cS, the division-free
calculation gives delta*uF=-uS, without requiring the common c to be an
integral unit, or even nonzero. If delta=-1, then uF=uS in this fixed cofactor
orientation. If cF differs from cS by an integral unit, (4)--(5) give the
required equality of valuations. Orientation changes alter a fixed unit sign,
not the valuation conclusion.

The common-zero case concerns zero functionals/evaluations in an otherwise
rank-one generic presentation. It does NOT extend the theorem to v=0 or a
generically acyclic constituent: eta != 0 explicitly excludes those branches.

## 6. Complement independence: the ratio is intrinsic

The cycle equations give AF v=-D0 hF and AS Jv=-D0 hS. Each closed functional
annihilates the common strict image. Thus both local cross-functionals vanish
on v:

    lambdaF AS J(v)=0,  lambdaS AF(v)=0.

They therefore descend to the one-dimensional quotient F/Lv. Every other
complement is x'=r x+s v with r != 0. Directly,

    eta'=r*eta, qF'=r*qF, qS'=r*qS, theta'=r^2*theta.

The terms involving D0 disappear from theta' by alternating multilinearity.
All coordinates and the ratio are unchanged. This is an ordinary proof in
this packet, with exact test coverage; no separate Lean declaration for the
quotient construction is claimed.

## 7. Countercontrol and what it excludes

Over Z_2 use

    DF=[[0,2],[0,0]], DS=[[0,0],[0,4]], J=diag(1,-1),
    zF=zS=e1, lambdaF=(0,1), lambdaS=(1,0).

The classes and functionals are primitive integral, local J is unimodular,
and both generic ranks are (1,1). But uF=-1/2 and uS=1/4. The transported
ratio is 2. For x=e2, qF=-4 and qS=2, so (2) records precisely that defect.

The example fails the common-normalization premise (6). It is not an
arithmetic counterexample. It proves why primitivity, integrality, local
volume and equal generic ranks cannot replace the boundary--cup adapter.

## 8. Formal scope

The formalization proceeds from raw D0, AF, AS, actual cycles,
closedness, nonzero local area and nonzero target determinant. It derives the
frame identities, both cofactor coordinates and their uniqueness, rather
than importing (1) as an assumption. The integral unit result explicitly
uses a lift of det J to R^units. The arithmetic-facing adapter quantifies
over all local vectors and uses the same stored lambdaF/lambdaS as the
matrix theorem.

Not formalized or established here: the actual arithmetic realization,
the occurrence of AxesKernel, compatible integral Selmer presentations,
Poitou--Tate naturality, passage through the inner/outer constructions, or
all exceptional height-one localizations. These are separate source
applications, not new assumptions that may silently be marked proved.
