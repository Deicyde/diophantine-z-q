# Quadratic S10 contact supplier and its reflected effective consumers

Author: internal model task `/root/sol61_height_foundation`, 2026-11-10. Author proposal, not independent acceptance. This selected H0–H4 text supplies the full-family height input for the 214 construction. Its scope is a complete connecting argument **relative to the inherited geometric, normalized modular-realization, modular-Jacobian height, root-height, scalar/anchor, rank and Lucas interfaces specified below**. It does not silently claim full published-source closure of those inherited proofs. Publication-version limitations are explicit in SOURCES.json and FINDINGS.md.

All heights h are absolute logarithmic Weil heights. All hF are original stable Faltings heights. Tate modules use arithmetic Frobenius and det(r_f)=epsilon*chi_cyc. Added algebraic scalar coefficients have trivial Galois action. Symbols for number fields, scalar characters and integer labels are kept distinct below.

## H0. Exact inherited interfaces and domain

Let `S={2,3,5,7,11,13,17,37,41,2399}`, `B_S=1857890364330`, and `E(R)=product_(p|R)(1+1/p)`. For every finite rational a=u/v in lowest terms, v>0, with `a notin {0,1,2401,-343/32}`, define M=M_S(a) to count once each p outside S having positive odd valuation on one of

`v,u,u-v,u-2401v,32u+343v`.

Put `R=B_S M` and ell=log R. R is squarefree; M=1 is allowed. The exact small-prime support argument is inherited from private#8 cutoff proof §1 and private#9 conductor proof §§1–3. It uses the same full three-marked normalizer fiber as the parent manuscript, not a substituted surface: its branch sections are the five indicated contacts; outside210, even contact is unramified after an unramified extension, including infinity. The normal fiber field L has degree dividing576, is unramified outside supp(R), defines all geometric homomorphisms between the conjugate surfaces, and A_a has good reduction over L away from210. The same surface satisfies

`h(a) <= 2 max(0,hF(A_a))+128`.                         (H0.1)

The CM branch gives `hF(A_a)<854R`, over the same support and metric. These uniform source statements apply to every a above, not only the later constructed beta or detector values. The non-CM surface has geometric endomorphism algebra the quaternion division algebra B of discriminant210, hence is absolutely simple. Its B-linear conjugate isogenies mu_sigma are L-defined, chosen with mu_1=1 and inflated from Gal(L/Q). The normalized sign cocycle and modularity-descent lemma are the actual parent `quartic_v14.tex` passages481ff,8110ff; the latter lemma accepts any locally constant scalar splitting satisfying its cocycle equation. It identifies the **original** r_5, with its finite twist absorbed into the final primitive weight-two form f. The companion trace argument identifies the original r_3 with that same f; neither the absorbed finite twist nor its kernel field replaces the controlled lift or L'.

The private#9 conductor argument applies to every controlled lift that is tame at odd primes and has scalar Dirichlet conductor dividing4 at2. It proves for this final f

`N <= C_N R²`, `rad(N)|R`, `C_N=2^68 3^16 5^16 7^4`. (H0.2)

Here is why the freedom used below preserves that argument: the torsion field E_tor=L(A[11]) is normal, `[E_tor:Q]` divides `576 |GL_4(F_11)|`, and the valuations of that integer at2,3,5,7 are15,4,4,1. Adjoining the kernel field of the scalar Dirichlet character and then the quadratic kernel of its lift adds at most two dyadic factors and only tame factors at odd primes. Thus `v_p(e)<=17,4,4,1`. The derivative/different calculation in private#9 §2 bounds the last positive upper break by2v_p(e), the Swan conductor of a two-dimensional representation by4v_p(e), and its tame codimension by2. Exponents70,18,18,6 follow. At p>7, L/Q is tame, A/L has good reduction and the scalar lift is trivial on wild inertia; exponent<=2 follows. The original r_5 is used at every p!=5 and original r_3 at5, so the level bound omits no prime. No bound on the tame part of e or the coefficient degree is substituted. This repeats the changed-lift connecting argument while retaining the parent published local-compatibility/modularity qualifications.

The retained modular-Jacobian project proof supplies, for `H=ker epsilon`, `J=Jac(X_1(N)/H)`, genus g>0 and actual j-map degree d,

`d=N s product_(p|N)(1+1/p)`, `g<=d`, `s=ord(epsilon)`,

`hF(J) <= d/2(log12+log N+2log d)+g log(2/sqrt(pi))`. (H0.3)

This is the differential-evaluation proof at Brox v17 Corollary4.3 (label cor:modularheight), not its large-primorial numerical theorem. It is retained as the precise versioned project height input already consumed by private#9. It is valid after arbitrary finite extension; the auxiliary field splitting its evaluation fiber contributes no degree to the isogeny estimate. The local expanded proofs height-evaluation.md, height-different.md, height-metric.md and height-assembly.md supply this interface.

## H1. Minimal two-primary characters and the actual normalized field

Let `U(R)=max({2} union {2^v2(p-1): p odd, p|R})`. At each odd prime where the sign cocycle has nontrivial local boundary, choose a generator g of the cyclic group modulo p and take the character sending g to a primitive `2^v2(p-1)` root of unity. Since `(p-1)/2` has exactly one fewer factor2, the character takes -1 to-1. Where the boundary is trivial choose the trivial local character. At2 choose the nontrivial character modulo4 only if its boundary is required. The product chi has order m dividing U(R), is tame at every odd prime and has conductor dividing4 at2.

This is a choice inside the parent's instruction to choose an odd local character; it changes the representation and final f and therefore needs the fresh comparison here. The parent's local reciprocity criterion for the constant-coefficient squaring sequence says that the boundary is nontrivial exactly when the local character takes -1 to-1. Hence the new chi has the same prescribed local boundaries as the original sign cocycle at every finite prime. The global Brauer injection/reciprocity argument used in the parent supplies the same sign-class equality, including the determined real invariant. A continuous pointwise square root, corrected by a sign cochain, gives

`b²=chi`, `delta b=epsilon_sign`, `b:G_Q -> mu_(2m)`.

Twist b by the parent's quadratic character to remove the finitely many unwanted inertia characters outside supp(R). This preserves b² and delta b, stays in mu_(2m), is tame at every odd added place, and adds possible support only at2, already in S. On G_L the sign cocycle is trivial, so b is a character, invariant under conjugation by G_Q. Its kernel field L' contains L, is normal over Q, and

`d'=[L':Q] <= 2m[L:Q] <=1152 U(R) <=2304 phi(R)`.    (H1.1)

The last deliberately conservative bound will be used numerically. Since the isogenies are inflated from Gal(L/Q) and mu_1=1, both mu_sigma and `a_sigma=(deg mu_sigma)^(-1/4)` equal1 on G_L. Consequently

`rho_l(sigma)=b(sigma)^(-1) a_sigma mu_sigma o sigma`

restricts on G_L' to the **actual Tate representation of this A_a**, not an unspecified scalar twist. The normalized cocycle identity makes rho_l a representation; the B-action gives `rho_l=r_l direct-sum r_l`. All geometric endomorphisms remain defined over L'. Faltings semisimplicity and the commutant `B tensor Qbar_l=M_2(Qbar_l)` imply that `r_l|G_L'` is absolutely irreducible. The parent modularity lemma applies with `t_sigma=a_sigma/b(sigma)`; changing chi has preserved every hypothesis, including finite local constancy. It supplies a final primitive weight-two f with `r_5=r_(f,5)`. The companion trace comparison supplies the same identity at3. For the multiplicity argument below one prime, say5, suffices; no assertion at a missing coefficient prime is needed.

On the fourth exterior power an isogeny acts by its degree, and Galois acts by chi_cyc². The normalization `a_sigma^4 deg(mu_sigma)=1` therefore gives `det rho_l=b^-4 chi_cyc²=chi^-2 chi_cyc²`. On the other hand the modular decomposition gives `det rho_l=epsilon² chi_cyc²`. Thus

`(epsilon chi)²=1` and `s=ord(epsilon) divides U(R)`. (H1.2)

Indeed U(R) is a power of two and is even; both chi and epsilon*chi have orders dividing it. Weight two gives epsilon(-1)=1, so -1 belongs to H. Finally `U(R)|phi(R)` and

`s E(R) <= U(R)E(R) <= phi(R)E(R)
 = R product_(p|R)(1-p^-2) < R`.                     (H1.3)

No uniform bound on U(R) or on the coefficient field is asserted. The finite twist absorbed while choosing f is not identified with chi; determinant(H1.2) uses the original normalized representation itself.

## H2. Multiplicity over L', not only geometric multiplicity

Let `E_f=Q(a_n(f): n>=1)`, e=[E_f:Q]. The modular abelian variety A_f is defined over Q, has dimension e, and over Qbar_5 its Tate module is the sum of the two-dimensional coefficient conjugates r_f^tau. This is the standard modular-factor input: published Shimura Theorem1 gives the quotient, dimension and differentials; its Euler-factor assertion requires the coefficient-conjugate span to be Fricke-stable. For the final primitive weight-two newform this condition is supplied by the Li Fricke formula in the actual parent modularity argument. Thus the formula applies to this f with arbitrary nebentypus, not only to a Gamma0 form. The Tate/cohomology dual convention is the same as that parent's modular identification. This is an explicit hypothesis match, not an appeal to a similarly named modular variety.

At every good place v of L' away from5 and the finitely many bad rational primes, `tr(r_f(Frob_v))=tr(V_5(A_a)(Frob_v))/2` is rational. The trace on the left belongs to E_f before any coefficient embedding: if v has residue degree f_v over rational p, it is the trace of the f_v-th power of a rational-prime Frobenius, a polynomial in a_p and p epsilon(p). The equality in the chosen embedding at5 to a rational number therefore identifies that E_f element with the same rational number. Every coefficient embedding fixes it. Chebotarev and semisimple character uniqueness identify every `r_f^tau|G_L'` with the same absolutely irreducible restricted representation W. Its semisimplicity also follows directly from that of the abelian variety Tate modules; a finite-index restriction here introduces no unproved extension-class replacement.

Consequently the Tate modules of `(A_f)_L'^2` and `A_a^e` have identical semisimple characters, already over Q_5. Faltings' isogeny theorem gives an L'-isogeny. In the semisimple L'-isogeny category, absolute simplicity of A_a forces every simple factor of (A_f)_L' to be isogenous to A_a over L'. Comparing dimensions proves e is even and

`(A_f)_L' is L'-isogenous to A_a^r`, `r=e/2`.         (H2.1)

The Hecke relation `a_p²-a_(p²)=p epsilon(p)` puts epsilon(p) in E_f for every p prime to N. Chebotarev for the finite cyclotomic quotient supplies primes in every invertible residue class modulo N, hence the complete image of epsilon lies in E_f. Therefore `Q(zeta_s) subset E_f`, so `r>=phi(s)/2`. If s>=4 is a power of two, phi(s)=s/2; if s=1 or2, use r>=1. In all cases

`s/r <=4`.                                         (H2.2)

Every coefficient conjugate of f has the same diamond-character kernel H, so all its differentials are fixed by H. For the quotient map X_1(N)->X_H, pullback identifies the Jacobian of X_H up to isogeny with the H-invariant subvariety. The A_f quotient restricted to that invariant subvariety is surjective, as seen on those differentials; characteristic zero makes this a genuine surjective homomorphism, not merely an equality of dimensions. Poincare reducibility over Q supplies a subvariety of J isogenous over Q to A_f. Base change and(H2.1) supply an **L'-defined** B_0 inside J_L' isogenous over L' to A_a^r. In particular g>=2r>=2. The field splitting a modular evaluation fiber and the coefficient value field are not substituted for L'.

## H3. Historical averaging route (superseded in this public application by height-averaging.md)

Take an L'-isogeny `A_a^r -> B_0`, and let `D_0=0 subset D_1 subset ... subset D_r=B_0` be the images of its first i factors. Each `C_i=D_i/D_(i-1)` is an L'-defined surface L'-isogenous to A_a. Rémond's stable subvariety/quotient inequality and Bost's lower bound `hF(C)>=-3 dim(C)/2` give

`sum_i hF(C_i) <= hF(B_0)
 <= hF(J)+3(g-2r)/2 <= H_J`,

where `H_J=max(1,hF(J)+3g/2)`. Thus one actual C_i has `hF(C_i)<=H_J/r`. No invariance of hF under isogeny is assumed.

Apply Gaudron–Rémond Theorem1.9(1) with reference variety C_i of dimension2, base field K=L', and extension equal to K. The published bound gives an L'-isogeny C_i->A_a of degree at most

`[14^32 d' max(1,log d',hF(C_i))]^16`.

The stable height increase along this direction is at most half the logarithm of that degree. Consequently, for any `X>=H_J/r` with `X>=1`,

`hF(A_a) <= X+8[32log14+log d'+log max(1,log d',X)]`. (H3.1)

The small surface C_i, its quotient maps and the final isogeny are all over L'. The growing multiplicity r is never used as an isogeny dimension. The published GR theorem's original stable normalization and both isogeny directions were checked directly in its final publisher PDF, pp7–8. Rémond's authorJune2021 source explicitly states the stable version after Corollary1.3; its final2022 journal body remains unavailable through the subscription redirect. This is a source-version coverage limitation, not a claim that the known inequality is false or unpublished.

## H4. S10 quadratic constant, all M>=1

Set `k=9339/1000`, `delta=10^-6`, `c0=8k+delta=74712001/1000000`, and `T=C_N R² E(R)`. By(H0.2),(H1.3), `logN<=logC_N+2ell`, `log d<logC_N+3ell`. Using(H0.3), g<=d and `log(2/sqrt(pi))<log2`, define

`K0=(log12+3log C_N)/2+log2+3/2`.

The rational interval certificate proves `4+K0/log B_S < k`. It follows that `H_J<=k d ell`, including its max with1, because k d ell>1. Equations(H2.2),(H0.3) then give

`H_J/r <=4k T ell = X`.

The same certificate proves `ell>=logB_S>28`, `log2304<logB_S`, `log(4k)+logC_N<4logB_S`. Hence(H1.1) gives `logd'<2ell`; and E(R)<R, logell<=ell give `logX<8ell`. Also X>max(1,logd'). From(H3.1), log14<3 and768<28ell,

`hF(A_a) < X+768+80ell < X+108ell`.

Combining with(H0.1), `216+128/logB_S < delta C_N B_S²`, gives

`h(a) < c0 C_N R² E(R) logR`.                       (H4.1)

The CM bound also satisfies(H4.1): `1708B_S+128<c0 C_N B_S² logB_S`, and the right side grows at least quadratically with R whereas1708R+128 is linear. Thus(H4.1) is uniform across both branches.

Define the exact positive real constant

`C2=c0 C_N B_S² E(B_S) logB_S`.

Since M is coprime to B_S, E(R)=E(B_S)E(M), and logR=logB_S+logM. Equation(H4.1) becomes

`h(a) < C2 M² E(M) [1+logM/logB_S]`.                (H4.2)

The portable rational certificate encloses each logarithm by an atanh series with a proved geometric tail. It proves strictly

`C2 < 2^(7557/32)`.

Every p outside S is at least19. With `theta0=log(20/19)/log19`, the positive ratio `log(1+1/p)/logp` is at most theta0: its numerator decreases and denominator increases for p>=19. Thus E(M)<=M^theta0. Also `1+logM/logB_S <= M^(1/logB_S)` by1+x<=exp(x). The certificate proves `theta0+1/logB_S<55/1024`. Consequently, including M=1,

`h(a) < C2 M^alpha`, `alpha=2103/1024`.              (H4.3)

This is a fresh small-support calculation. The false large-primorial shortcut `C_N²<B_S` is never used.

