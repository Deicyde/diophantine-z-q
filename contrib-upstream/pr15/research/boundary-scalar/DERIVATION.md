# Common-strict boundary-scalar comparison

## 0) Problem restatement (brief)

The supplied review of `40d01c5` contains the ordinary matrix theorem below.
Its archive is preserved byte-for-byte in [inputs](inputs/). The reviewed
six-lemma source and old exact checker agree with the current branch at intake
commit `083344e`. They establish supporting kernel/image and volume identities;
they do not compute the actual class-functional comparison. This addition
proves the matrix consequence and states a typed boundary--cup adapter.

The supplied derivation is credited to its reviewing assistant, who reports
having helped formulate the original candidate. Its rereview is not independent
self-acceptance. Our separately authored mathematical review and Lean checking
are recorded in the verification report. No literature-novelty claim is made.

## 1) Assumptions ledger

Work first over a field L. For the integral interpretation, let R be a DVR
embedded in L as its fraction field. Fix n≥2, m=n−2, and ordered bases. Classes
are columns; functionals are rows. Put

```math
D_F=[D_0\mid A_F],\qquad D_S=[D_0\mid A_S],
```

where D₀ has m columns, each A has two columns, and both square matrices have
n rows. In the integral application these matrices are over R. Their common
strict complex is `[R^m --D₀--> R^n]`, in degrees one and two; the quotient
complexes are the finite and singular planes in degree one.

Retain the actual cycles `z_F=(h_F,v)` and `z_S=(h_S,Jv)`, with v≠0 and
integral J invertible. Set δ=det J, an R-unit. Choose x over L such that
η=det[v,x]≠0. The complement may be fractional. Assume

```math
a=A_Fx,\quad b=A_SJx,\quad T=[D_0\mid a\mid b],\quad
\theta=\det T\ne0.
```

This includes rank(D₀)=m. Let λ_F,λ_S be nonzero closed L-valued rows:
`λ_F D_F=0`, `λ_S D_S=0`. They are the supplied functionals, with no independent
rescaling or primitive replacement. Define

```math
q_F=\lambda_F(b),\qquad q_S=\lambda_S(a).
```

The matrix theorem uses no valuation. The DVR and integrality are needed only
to interpret δ and the final unit/valuation criterion. A presentation of the
actual arithmetic complexes and the boundary--cup identities are still
application obligations; they are not supplied by these matrix assumptions.

## 2) Lemma-by-lemma resolution

**L1 — PROVED: common-strict basis reduction.** Use source matrices
`B_F=[e₁,…,e_m,z_F,(0,x)]` and `B_S=[e₁,…,e_m,z_S,(0,Jx)]`.
Their determinants are η and δη. The strict parts h_F,h_S do not affect these
block triangular determinants. The cycle equations give

```math
D_FB_F=T N_F,\qquad D_SB_S=T N_S,
```

where each N is identity on the first m coordinates, and its final block is

```math
N_F=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad
N_S=\begin{pmatrix}0&0\\0&1\end{pmatrix}.
```

This construction from the displayed D₀/A matrices is ordinary algebra in this
derivation. The Lean matrix theorem accepts the exact normal-form equations
and basis-determinant relations explicitly. It does not formalize construction
of a complex, quotient, or determinant functor.

**L2 — PROVED: closed rows determine the cross coordinates.** Closedness kills
D₀ and a for λ_F, and D₀ and b for λ_S. Thus in the common target basis the
rows have final blocks `(0,q_F)` and `(q_S,0)` and vanish on the strict block.
Since T is invertible, a nonzero row cannot vanish on every column of T;
therefore both q values are nonzero. This conclusion follows from closedness
and nonzero functionals, not from an assumed determinant comparison.

**L3 — PROVED: canonical tensor identities and basis transport.** Let e_p be
the first vector in the final block and e_q the second. The full adjugates are
`adj(N_F)=-e_p e_q^t` and `adj(N_S)=e_p e_p^t`. Consequently the corresponding
canonical class-functional tensors have coordinates −q_F and q_S.

For completeness, if `D B=T N`, `z=B z'`, `λ T=λ'`, and
`z'λ'=c adj(N)`, adjugate multiplicativity gives

```math
\operatorname{adj}(B)\operatorname{adj}(D)
 =\operatorname{adj}(N)\operatorname{adj}(T).
```

Multiply on the left by B and on the right by T:

```math
\det(B)\operatorname{adj}(D)T
 =\det(T)B\operatorname{adj}(N).
```

Also `(zλ)T=B(z'λ')=c B adj(N)`. Since det(T)≠0 and right multiplication by T
is injective, these equalities imply the full, entrywise tensor identity

```math
z\lambda=\frac{c\det B}{\det T}\operatorname{adj}(D).
```

This derivation does not require cancelling a torsion factor or an integral
complement. It is the basis of the formal transport theorem.

**L4 — PROVED: comparison and R-unit criterion.** Substituting L1 and L2 into
L3 computes

```math
u_F=-\frac{\eta q_F}{\theta},\qquad
u_S=\frac{\delta\eta q_S}{\theta},\qquad
\delta\frac{u_F}{u_S}=-\frac{q_F}{q_S}.
```

In the explicit inverse-determinant bases, the two common-strict sequences
and J give the comparison coefficient δ: the strict wedge is shared and the
local two-dimensional wedge is multiplied by det J. Hence the last expression
is the comparison of the distinguished class-functional tensors in this
cofactor convention. This interpretation is an ordinary determinant-line
argument; the Lean matrix theorem proves the concrete tensor identities and
scalar formula.

Every denominator is nonzero by the ledger. Since δ is an R-unit,

```math
v_R(u_F)-v_R(u_S)=v_R(q_F)-v_R(q_S).
```

Thus valuation preservation is equivalent to q_F/q_S lying in R×. The formal
unit corollary uses an actual unit of a coefficient ring R mapped into L;
it does not substitute `IsUnit` in the field for being an R-unit. The DVR
valuation statement itself remains the ordinary consequence displayed here.

**L5 — PROVED CONDITIONALLY: a typed boundary--cup adapter.** Let F and S be
possibly different modules and J:F≃S. Let ω be an alternating bilinear form on
F and define

```math
\beta(f,s)=\varepsilon\,\omega(f,J^{-1}s).
```

In the displayed two-term model, take `H=L^n/im(D₀)`,
`d_F(f)=[A_F f]` and `d_S(s)=[A_S s]`. Since each closed row kills D₀, it
descends to a functional on H. The two adapter evaluations are then exactly
q_F and q_S of L2. This quotient construction is part of the ordinary bridge
here; the Lean adapter works with the supplied modules and linear maps.

For the supplied boundary maps and functionals, assume the two actual
adjunctions

```math
\lambda_F(d_Ss)=c\,\beta(v,s),\qquad
\lambda_S(d_Ff)=-c\,\beta(f,Jv).
```

At s=Jx and f=x, inverse cancellation and alternation give

```math
q_F=c\varepsilon\omega(v,x)
 =-c\varepsilon\omega(x,v)=q_S.
```

No application of J to an element of S is required. In chosen coordinates
where the source's involution has J⁻¹=J this agrees with the supplied adapter.
The equality permits a nonunit c. Nonzero q values come from L2; alternatively
one can supply nonzero c, ε and ω(v,x). Alternation alone does not establish
nonvanishing of the pairing.

With distinct factors c_F,c_S the evaluations instead retain those respective
factors. Their quotient can have a nonzero valuation. The formal adapter
retains the maps and functionals and proves only the consequences of these
lower-level identities; it does not prove their arithmetic occurrence.

## 3) Main theorem

**PROVED in the explicit common-strict presentation:** the determinant
discrepancy is exactly −q_F/q_S in the declared convention. The common target
denominator θ cancels, including any nonunit strict contribution. Divisible
actual vectors and nonzero strict components remain in the calculation.

**OPEN for the arithmetic application:** construct the compatible presentation
and identify the actual duality-defined functionals and adjunctions at every
required localization. In particular the shared c in L5 must be proved from
the retained arithmetic maps, cochains and signs. No normalization is selected
merely to obtain the answer. No assertion through either uniform limit follows
from this matrix calculation alone.

## 4) If refuted: repaired statement

The weaker implication from local J, axes, integrality and primitivity alone
is refuted. Over Z₂ take

```math
D_F=\begin{pmatrix}0&2\\0&0\end{pmatrix},\quad
D_S=\begin{pmatrix}0&0\\0&4\end{pmatrix},\quad
J=\operatorname{diag}(1,-1),\quad z_F=z_S=v=e_1,
```

and primitive closed rows λ_F=(0,1), λ_S=(1,0). The common strict complex is
R² in degree two. Both generic kernel lines and the combined axes have the
specified form. The tensor coordinates are −1/2 and 1/4, with comparison 2.
Here q_F=−4 and q_S=2, so the exact formula detects the discrepancy. The
cokernels have torsion R/(2) and R/(4), respectively: local class-line
quotients do not determine boundary-image indices.

The valid repair is an actual unit ratio of the cross evaluations, for example
the same boundary--cup normalization of L5. This example lacks that hypothesis
and gives no counterexample to the arithmetic manuscript.

## 5) Verification plan for the verifier role

Independently re-derive the cofactor sign and determinant-line δ, check all
nonzero premises, and compare the exact elaborated Lean statements with L1–L5.
Check n=2, characteristic two, divisible vectors, fractional complements,
nonunit common normalization, and distinct boundary-image indices. Run the
supplied exact checker normally and under optimization, retaining its finite
scope. Compare the ordinary common-strict bridge with the formal normal-form
inputs; do not silently promote the former into Lean coverage. Check every
new Open Math target and preserve the old frozen packet and accepted source
snapshot. Native local checking uses pinned Lean 4.35 without `--paranoid`;
the protected cloud run remains Open Math's later execution step.
