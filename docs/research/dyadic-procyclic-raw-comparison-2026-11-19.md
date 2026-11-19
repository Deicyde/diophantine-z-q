# All-degree raw comparison for a dyadic-by-procyclic extension

**Status.** Hand mathematics under the stated topological and coefficient hypotheses; this text is not machine-checked or end-to-end formally verified. It does not identify or verify an original arithmetic instance, prove that the integers are Diophantine in the rationals, or settle Hilbert’s tenth problem over the rationals.

## Theorem

Let Q be a compact Hausdorff group with a given open-normal identity-neighborhood basis. Let rho:Q→C be a continuous surjective homomorphism with literal kernel N, and let e_N:N→Z_2 and e_C:C→Zhat be given topological group isomorphisms onto the additive groups. Put n_x=e_N⁻¹(x), h=n_1 and gamma=e_C⁻¹(1). Assume a given continuous homomorphic section sigma:C→Q with rho sigma=id, and a continuous character u:C→Z_2^× satisfying

  sigma(c)n_xsigma(c)⁻¹=n_(u(c)x).

Put q=sigma(gamma), u_0=u(gamma). Let M be any discrete 2-primary torsion abelian group with its given jointly continuous full Q-action R_g by additive automorphisms. No finiteness, uniform annihilator, trivial N-action, scalar C-action or projectivity is assumed.

Write T_x=R_(n_x), T=T_1, V_c=R_(sigma(c)), V=V_gamma. Use the continuous local dyadic norms S_x(T) and put

  P_c=S_(u(c))(T), P=P_gamma, W_c=P_c⁻¹V_c.

The actual raw additive coefficient complex is

  K_M^0=M, K_M^1=M⊕M, K_M^2=M, K_M^n=0 otherwise,
  d^0m=((T−1)m,(V−1)m),
  d^1(a,b)=(V−P)a−(T_(u_0)−1)b.

For g∈Q put c_g=rho(g), n(g)=g sigma(c_g)⁻¹ and x_g=e_N(n(g)). Define

  f_(a,b)(g)=S_(x_g)(T)a+T_(x_g)B_b^V(c_g),
  kappa_p(g,g')=T_(x_g)S_(u(c_g)x_(g'))(T)B_p^W(c_g),
  j_M^0=id, j_M^1(a,b)=f_(a,b), j_M^2(t)=kappa_(P⁻¹t),
  j_M^n=0 from the zero source groups for n≥3.

Here B_a^V and B_a^W are the actual continuous crossed maps on C with generator value a. Then:

1. j_M is an additive chain map to the untruncated continuous cochain complex C_Q^*(M), with the standard signed full-action differential.
2. H^n(j_M) is bijective for every n≥0. In particular every actual continuous Q-cocycle in degree n≥3 has a continuous primitive.
3. For a full-Q-equivariant additive coefficient map F:M→M', the graded map K(F) has components F,F⊕F,F and zero-group maps elsewhere, and

     C_Q(F)j_M=j_(M')K(F)

   strictly as cochain maps. The induced cohomology bijections are natural.
4. If whole R-module structures with R-linear full Q-actions are separately given, these maps and bijections are R-linear. The higher primitives constructed below are existence statements and are not claimed canonical, additive, natural or R-linear choices.

The raw degree-two normalization is essential: j_M^2(t)=kappa_(P⁻¹t). Its cohomology inverse first takes the normalized class coordinate and then applies the quotient P. No strict inverse of the infinite continuous cochain complex or contraction of the given M-complex is claimed.

This proof assembles the established direct low-degree comparison with the established conditional coinduction lemma. The load-bearing new fit is that the actual coinduced modules satisfy every low-degree coefficient hypothesis, and their actual class maps discharge the conditional degree-two premise. Those hypotheses are verified below, not accepted as data.

## 1. The fixed group, coefficient class and signed complex

The actual kernel-section equations are

  g=n_(x_g)sigma(c_g),
  c_(gg')=c_gc_(g'), x_(gg')=x_g+u(c_g)x_(g'),
  R_g=T_(x_g)V_(c_g), V_cT_xV_c⁻¹=T_(u(c)x).     (1.1)

Membership n(g)∈N follows from rho sigma=id, and multiplication gives the other equations. The coordinates are continuous on the given group and subgroup topologies. No replacement product model is being introduced.

Let A_Q be the class of discrete abelian groups X killed elementwise by powers of 2, with jointly continuous full Q-actions R^X by additive automorphisms. This is exactly the coefficient class used below. For any X∈A_Q, its restricted operators T_z^X=R^X_(n_z), V_c^X=R^X_(sigma(c)) have the same group conjugation character u. No additional coefficient action or ring is assigned.

Canonical Z_2 scalars on X are defined elementwise by integer residues at an annihilating exponent. All additive maps preserve them, since the same exponent kills the image. They commute with additive action operators but do not make those operators scalar.

For X∈A_Q let C_Q^n(X)=Cont(Q^n,X), C_Q^0(X)=X, with

  (D_X^n f)(g_1,...,g_(n+1))
   =R^X_(g_1)f(g_2,...,g_(n+1))
    +sum_(i=1..n)(−1)^i f(...,g_i g_(i+1),...)
    +(−1)^(n+1)f(g_1,...,g_n).                   (1.2)

All terms preserve continuity. For n≥1 define H^n=ker D_X^n/im D_X^(n−1); H^0=ker D_X^0. A zero class means an actual continuous coboundary.

The standard equality D_X^(n+1)D_X^n=0 holds in every degree. It follows through the continuous homogeneous dictionary

  f(g_1,...,g_n)=F(1,g_1,g_1g_2,...,g_1...g_n),
  F(y_0,...,y_n)=R^X_(y_0)f(y_0⁻¹y_1,...,y_(n−1)⁻¹y_n),

where F is equivariant for simultaneous left multiplication. First-vertex deletion gives the full leading action, interior deletion merges adjacent factors, and final deletion gives the last sign. Two deleted original positions a<b occur in the two orders with signs (−1)^(a+b−1) and (−1)^(a+b); they cancel and exhaust the double sum. This is valid for nonabelian Q. Additive full-Q-equivariant postcomposition commutes with (1.2).

Negative terms, when mentioned, are formal zero groups. No positive continuous cochain group is made zero.

## 2. The established universal low-degree interface, with its actual formulas

We use the direct low-degree comparison lemma for the given Q and every X∈A_Q. To specify both its dependency and the needed full-action calibration, we recall its construction and conclusions here.

### 2.1. Local norms and the corrected C-action

For each a∈X, continuity of its N-orbit and 2-primary torsion give local integers k,r with T_(2^kz)^Xa=a and 2^r a=0. The actual additive T-orbit span is finite, stable under T, and killed by 2^r; no span over an auxiliary ring is claimed. On common such bounds the finite operator norm has period 2^(k+r). Evaluating an integer representative of x at that period defines S_x(T^X)a independently of the representative and bound. Common bounds prove coefficient additivity and joint evaluated continuity, including the pullback action T^(y):z↦T_(yz).

The finite polynomial sum, product and telescope laws give

  S_(x+y)(T)=S_x(T)+T_xS_y(T),
  S_x(T)(T−1)=T_x−1,
  S_(xy)(T)=S_x(T)S_y(T^(x)),
  S_a(T)⁻¹=S_(a⁻¹)(T^(a)) for a∈Z_2^×.      (2.1)

Both inverse orders follow by applying the product law to T and T^(a). All local T-polynomials commute with one another, not with arbitrary V_c. Conjugation gives V_cS_y(T)V_c⁻¹=S_y(T^(u(c))). The finite polynomial identity S_n(T)−n=(T−1)sum_(j<n)S_j(T) gives an actual per-element witness for

  (S_x(T)−x id)X⊂(T−1)X.                   (2.2)

No global exponent or finite-cyclic cohomology comparison is used.

For P_c^X=S_(u(c))(T^X), put K_(c,d)^X=S_(u(d))((T^X)^(u(c))). Then

  P_(cd)^X=P_c^XK_(c,d)^X,
  V_c^XP_d^X(V_c^X)⁻¹=K_(c,d)^X.

The commuting unit norms imply W_c^X=(P_c^X)⁻¹V_c^X is a genuine C-action. Evaluated unit-inverse continuity and continuity of V give joint continuity of W. The exact intertwining identities are

  S_(u(c)y)(T^X)W_c^X=V_c^XS_y(T^X),
  (T^X−1)V_c^X=W_c^X(T^X−1).                (2.3)

These are derived operator equations on the given coefficient group, not a new full Q-action on the raw terms.

For either actual C-action V or W, the orbit of a is finite by compactness. Its finite additive span has a true generator operator order d, possibly with odd factors, and local annihilator 2^r. Norm sums at the full period d2^r define the continuous crossed map

  B_a^X(c)=S_(red_(d2^r)e_C(c))(X_gamma)a

for that C-action. They satisfy B_a(cd)=B_a(c)+X_cB_a(d), B_a(1)=0 and B_a(gamma)=a. Signed generator powers and density prove uniqueness; common bounds prove additivity and intertwiner naturality. The odd part of d is retained. Dyadic crossed maps are similarly x↦S_x(T)a.

### 2.2. All-element chain identities and H^0,H^1

For every coefficient X the raw maps in the theorem are defined using these actual norms and crossed maps. Define

  E_(a,b)(c)=(W_c−1)a−(T−1)B_b^V(c).

By (2.3), E_(a,b) is W-crossed with generator value P⁻¹d^1(a,b). Expanding the three signed terms of D^1f at g=n_xsigma(c),g'=n_ysigma(d) gives

  D^1f_(a,b)(g,g')
    =T_x[V_cS_y(T)a−S_(u(c)y)(T)a
                  −(T_(u(c)y)−1)B_b^V(c)]
    =kappa_(P⁻¹d^1(a,b))(g,g').              (2.4)

Thus this is an all-pair identity, not merely a generator test. Also f_(d^0m)=D^0m by telescope and the V-crossed uniqueness. Conjugation and P(T−1)=T_(u_0)−1 give d^1d^0=0.

Closedness of every kappa_p is checked independently. Put A_p(c,y)=S_(u(c)y)(T)B_p^W(c). It obeys

  A_p(c,y+z)=A_p(c,y)+T_(u(c)y)A_p(c,z),
  A_p(cd,z)=V_cA_p(d,z)+A_p(c,u(d)z).

For three factors n_xsigma(c),n_ysigma(d),n_zsigma(e), with v=u(c),w=u(d), the four signed D^2kappa terms are

  +T_xT_(vy)V_c A_p(d,z),
  −T_xT_(vy)[V_cA_p(d,z)+A_p(c,wz)],
  +T_x[A_p(c,y)+T_(vy)A_p(c,wz)],
  −T_xA_p(c,y).

They cancel without assuming that kappa is a boundary. Consequently

  D^0j^0=j^1d^0, D^1j^1=j^2d^1, D^2j^2=0,
  f_(a,b)(h)=a, f_(a,b)(q)=b,
  kappa_p(q,h)=Pp, kappa_p(n,g)=0 for n∈N.    (2.5)

The h/q zero-cocycle test follows by continuity and density of signed h-powers and sigma(gamma)-powers. Every continuous one-cocycle f restricts to S_x(T)f(h) on N and B_(f(q))^V on sigma(C), then its crossed product equation gives f=f_(f(h),f(q)). Equation (2.4) at (q,h) forces d^1(f(h),f(q))=0; conversely d^1=0 makes the whole cochain closed. Its boundaries have h/q coordinates d^0. Hence

  H^0_cont(Q,X)=ker(T^X−1)∩ker(V^X−1),
  H^1_cont(Q,X)≅ker d_X^1/im d_X^0.          (2.6)

No perfect cup pairing or group presentation is used.

### 2.3. Fresh normalized H^2 and its precise primitive inputs

The only cocycle-primitive existence inputs in the low-degree lemma are the direct finite-column degree-two primitive theorems for N≅Z_2 and C≅Zhat. Each applies to every discrete 2-primary coefficient group with its actual restricted continuous action and gives a unique generator-zero primitive, with identity value equal to the cocycle's identity value. Their period constructions and signed residual-density proof do not use a finite-cyclic cohomology comparison. The N theorem is applied with the actual T-action; the C theorem with the actual V-action. The section here is given as a continuous homomorphism.

For a continuous two-cocycle z with values in any X∈A_Q, the direct low-degree construction proceeds as follows, recording the signs because they will give actual boundary witnesses later:

1. Put a_0=z(1,1). Its edge values are z(1,g)=a_0 and z(g,1)=R_g^Xa_0. If c_0 is the constant one-cochain a_0, D^1c_0(g,g')=R_g^Xa_0. Thus z_norm=z−D^1c_0 is normalized.
2. Use the direct N primitive b_N, with b_N(h)=b_N(1)=0, on z_norm|_(N×N). Extend by E_N(g)=b_N(n(g)); z_0=z_norm−D^1E_N kills N×N.
3. Set alpha(g)=z_0(n(g),sigma(c_g)). It vanishes on N and sigma(C). Since D^1alpha(n,sigma(c))=−z_0(n,sigma(c)), the cocycle z_1=z_0+D^1alpha kills N×sigma(C). The law at (n,n',sigma(c)) then kills N×Q; the PLUS sign is required.
4. On the section square use the direct C primitive b_C for the actual V-action, with b_C(gamma)=b_C(1)=0. Put S_C(g)=T_(x_g)b_C(c_g). Then S_C(ng)=R_n^XS_C(g), S_C(n)=0 and D^1S_C(n,g)=0. Thus z_2=z_1−D^1S_C kills both N×Q and sigma(C)².
5. For such a residual F, the actual cocycle equations give F(g,g')=T_(x_g)A(c_g,x_(g')) with A(c,y)=F(sigma(c),n_y), and

     A(c,x+y)=A(c,x)+T_(u(c)x)A(c,y),
     A(cd,y)=V_cA(d,y)+A(c,u(d)y).

   The first law gives A(c,y)=S_y(T^(u(c)))A(c,1). The second, together with P_cd=P_cK_(c,d) and V_cP_d=K_(c,d)V_c, says beta(c)=P_c⁻¹A(c,1) is W-crossed. Hence beta=B_p^W for p=beta(gamma), and F=kappa_p as a cochain.

The trailing identity F(sigma(c),n_ysigma(d))=A(c,y) used in step 5 follows from the law at (sigma(c),n_y,sigma(d)) and the already zero section square. All coordinates are actual group coordinates. Combining the corrections gives

  z=kappa_p+D^1b_z,
  b_z=c_0+E_N−alpha+S_C∈C_Q^1(X).            (2.7)

This proves surjectivity of the actual class map Phi_X(p)=[kappa_p] for every X∈A_Q, with a continuous boundary witness.

If kappa_p=D^1b, normalization makes b(1)=0 and N-first zero makes b|N crossed. Then b(n_(u_0))=Pb(h). Comparing D^1b(q,h) and D^1b(n_(u_0),q), using qh=n_(u_0)q, gives

  Pp=d^1(b(h),b(q)).                         (2.8)

Conversely (2.4) gives every such kappa boundary. Let

  mathfrak j_X=(T^X−1)X,
  mathfrak a_X=mathfrak j_X+(V^X−u_0 id)X.

Unit norms and (2.2) imply

  im d_X^1=mathfrak a_X,
  P_X mathfrak a_X=mathfrak a_X=P_X⁻¹mathfrak a_X,
  ker Phi_X=mathfrak a_X.                    (2.9)

Indeed (T_(u_0)−1)X=mathfrak j_X, (P_X−u_0)X⊂mathfrak j_X and V_Xmathfrak j_X=mathfrak j_X. On the actual quotient X/mathfrak j_X, P_X is the invertible canonical scalar u_0; its inverse is u_0⁻¹ and both preserve the image of V_X−u_0. P_X has not been made scalar on the whole X.

Thus the established universal low-degree result supplies actual additive bijections

  barPhi_X:X/mathfrak a_X→H^2_cont(Q,X),
  p+mathfrak a_X↦[kappa_p^X]                 (2.10)

for every X∈A_Q. They are natural for full-Q-equivariant additive maps F. More strongly, the formulas give

  F kappa_p^X=kappa_(Fp)^(X'),
  C_Q(F)j_X=j_(X')K(F)                      (2.11)

strictly on cochains. This is the low-degree interface now reused, not a assumed higher-vanishing predicate.

The raw degree-two cohomology comparison is barPhi_X o barP_X⁻¹, with inverse barP_X o barPhi_X⁻¹. The latter first takes the normalized class coordinate, then applies the quotient P.

## 3. Uniform finite-image control on the actual profinite group

We use the unconditional finite-factorization part of the coinduction lemma and expose its proof for the coefficient fit. For a continuous f:Q^k→S into any discrete set, k≥1, each point has a box p_1U_p×...×p_kU_p inside its fiber, with U_p an open normal subgroup chosen from the given basis. Finitely many boxes cover compact Q^k. Let U be their common intersection. If x is in one box and u_i∈U, then x_i u_i stays in that same box because U⊂U_p. Hence

  f(x_1u_1,...,x_ku_k)=f(x_1,...,x_k)          (3.1)

for every x and u_i∈U. No commutativity is used. The subgroup U has finite index: its open cosets cover compact Q and admit a finite subcover. Therefore f has finite image and uniform right-U invariance in all coordinates. For k=0 the domain is one point.

In particular this applies when the discrete target is an infinite function group. Uniform equality there is equality of whole functions, not merely equality at each evaluation point with a different neighborhood.

## 4. The actual envelope and every low-degree coefficient hypothesis

Fix arbitrary M∈A_Q. Define

  I_env(M)=Cont(Q,M_underlying), with pointwise addition and DISCRETE topology,
  (R^I_g F)(x)=F(xg),
  iota_M(m)(x)=R_xm,
  J_env(M)=I_env(M)/iota_M(M), with DISCRETE topology,
  pi_M:I_env(M)→J_env(M) the actual quotient map.   (4.1)

These are the exact auxiliary modules of the coinduction lemma, not replacements for M or the additive parameter subgroups mathfrak a_X, mathfrak j_X.

We verify their class membership in full:

- I_env is an abelian group: sums and negatives of continuous functions are continuous, and the laws hold pointwise.
- Each F has finite image by (3.1). A local power 2^r killing those finitely many values kills the function F. Thus I_env is 2-primary, possibly infinite and of unbounded exponent; it is not an unrestricted product of all set-theoretic functions.
- Right translation sends continuous functions to continuous functions and is additive, with inverse right translation by g⁻¹. For nonabelian Q the action order is

    (R^I_g R^I_h F)(x)=F(xgh)=R^I_(gh)F(x).

  Thus this is a LEFT full Q-action, with the given right-translation formula and no reversal.
- Choose U from (3.1) for F, so F(yu)=F(y). For g'∈gU, R^I_(g')F(x)=F(xg')=F(xg)=R^I_gF(x) for ALL x. The orbit map into discrete I_env is locally constant. Equivalently each stabilizer is open; since I_env is discrete, the full action Q×I_env→I_env is jointly continuous. This is uniform over x.
- For each m, x↦R_xm is continuous by the given joint continuity of the original action, so iota(m) belongs to I_env. It is additive and ev_1 iota=id, hence injective. Its actual equivariance is

    iota(R_gm)(x)=R_xR_gm=R_(xg)m=R^I_g iota(m)(x).

  The image is a genuine Q-stable subgroup. Evaluation at 1 is not asserted a Q-equivariant splitting to the original action on M.
- J_env is a discrete abelian 2-primary quotient, with the induced full action. A representative F of a class has an open stabilizer that also fixes its class, so the quotient action is jointly continuous. pi is additive, onto and full-Q-equivariant, with kernel iota(M).

Therefore I_env(M) and J_env(M) satisfy EVERY coefficient assumption of the universal low-degree result. This proves the fit for the actual infinite modules, not for selected finite tests. The group-specific hypotheses Q,B,rho,N,e_N,e_C,h,q,sigma,u are exactly unchanged.

Their actual restricted operators are

  (T_z^I F)(x)=F(xn_z),
  (V_c^I F)(x)=F(xsigma(c)),

and T^J,V^J are the induced quotient operators. They satisfy the group conjugation relation because R^I is a genuine Q-representation. P_c^I and P_c^J are the local norms for THESE actions; W_c^I=(P_c^I)⁻¹V_c^I and W_c^J=(P_c^J)⁻¹V_c^J. No pointwise use of the original M-action has been substituted for right translation, and no trivial N-action or scalar V-action is inferred.

## 5. Exact continuous cochain lifting and its limitations

The unconditional lifting part of the coinduction lemma gives, for every k≥0,

  0→C_Q^k(M) --iota_*--> C_Q^k(I_env) --pi_*--> C_Q^k(J_env)→0.  (5.1)

Here the exactness is proved directly. If a continuous cochain F has all values in ker pi=iota(M), then

  F=iota o y, y=ev_1 o F.

Evaluation at 1 is a map between discrete groups, so y is continuous. It is unique by injectivity of iota. Conversely such values are in the kernel. This includes k=0.

For a continuous J_env-valued cochain w with k≥1, its finite image has clopen fibers by compactness and discreteness. Choose one I_env preimage for each image value and put that constant preimage on the corresponding fiber. The lift W is continuous and pi W=w. For k=0 choose one element. These are finite piecewise choices; no additive, R-linear, natural or canonical section of pi is asserted.

Both iota_* and pi_* commute with every signed D because the coefficient maps are actually additive and full-Q-equivariant. No long exact sequence or abstract coinduced-acyclicity theorem is being invoked.

## 6. Positive contraction, with uniform continuous types and nonabelian order

For n≥1 and f∈C_Q^n(I_env), the unconditional coinduction lemma defines

  (theta^n f)(g_1,...,g_(n−1))(x)
     =f(x,g_1,...,g_(n−1))(1).               (6.1)

The right side is an M-value: f(x,row) is an element of I_env, then evaluated at 1. For each row, it is an actual continuous function of x and hence an element of I_env. More importantly, (3.1) applied to f:Q^n→DISCRETE I_env provides one common U such that changing any variable on the right by U does not change the WHOLE value f(x,row). It follows simultaneously that

  (theta^n f)(row)(xu)=(theta^n f)(row)(x),
  (theta^n f)(g_1u_1,...,g_(n−1)u_(n−1))=(theta^n f)(row)

as elements of I_env. Thus theta^n f is continuous INTO the discrete I_env, not merely pointwise continuous after evaluation. For n=1 it is the single function x↦f(x)(1). The operator theta is additive.

For every n≥1,

  D_I^(n−1)theta^n f+theta^(n+1)D_I^n f=f.   (6.2)

To check the signs and order, evaluate at row g_1,...,g_n and x. The theta D term is

  f(row)(x)−f(xg_1,g_2,...,g_n)(1)
  +sum_(i=1..n−1)(−1)^(i+1)f(x,g_1,...,g_i g_(i+1),...,g_n)(1)
  +(−1)^(n+1)f(x,g_1,...,g_(n−1))(1).

The first value uses (R^I_x f(row))(1)=f(row)(x). The D theta term is

  f(xg_1,g_2,...,g_n)(1)
  +sum_(i=1..n−1)(−1)^i f(x,g_1,...,g_i g_(i+1),...,g_n)(1)
  +(−1)^n f(x,g_1,...,g_(n−1))(1).

Its leading value uses R^I_(g_1)(theta f(...))(x)=(theta f(...))(xg_1). Every value except f(row)(x) cancels. The order is xg_1 in BOTH terms, even for nonabelian Q.

For n=1 the middle sums are empty: theta^2D^1f(g)(x)=f(g)(x)−f(xg)(1)+f(x)(1), while D^0theta^1f(g)(x)=f(xg)(1)−f(x)(1). In degree zero theta^1D^0F=F−constant(F(1)), NOT F. Consequently every positive I_env-valued cocycle z is D(theta^n z), including degree two. This proves H^n_cont(Q,I_env(M))=0 for n≥1; it does not prove H^0=0 or a contraction of the original M-complex.

## 7. Actual Phi at BOTH auxiliaries and discharge of the degree-two condition

Having verified I_env,J_env∈A_Q in section 4, apply the actual universal low-degree theorem of section 2 to BOTH. It defines their literal normalized class maps

  Phi_I(p)=[kappa_p^I], p∈I_env,
  Phi_J(p')=[kappa_(p')^J], p'∈J_env,

with their actual T,V,P,W operators just described. It gives the additive bijections I_env/mathfrak a_I→H^2(Q,I_env) and J_env/mathfrak a_J→H^2(Q,J_env), in particular surjectivity at J_env. The coefficient subgroups mathfrak a_I,mathfrak a_J are not the envelope modules themselves.

pi is an actual additive full-Q-equivariant map. Thus pi T_z^I=T_z^J pi and pi V_c^I=V_c^J pi. The low-degree local norm construction gives

  pi S_y(T^I)=S_y(T^J)pi,
  pi(P_c^I)⁻¹=(P_c^J)⁻¹pi,
  pi W_c^I=W_c^Jpi.

The continuous crossed maps have the same generator coordinate, so their uniqueness gives pi B_p^(W^I)=B_(pi p)^(W^J). Retaining the actual group coordinates in the kappa formula yields the STRICT cochain identity

  pi kappa_p^I=kappa_(pi p)^J.               (7.1)

It follows, rather than being assumed, that

  H^2(pi)Phi_I(p)=Phi_J(pi p).               (7.2)

The low-degree theorem was proved for EVERY X∈A_Q, not only for the original M or finite modules. Its general quotient bijection and naturality therefore supply the universal natural degree-two interface of the conditional coinduction lemma. In particular the required maps exist at BOTH I_env and J_env, are onto at J_env, and are natural along their actual projection. No new action on a raw term or independent equivariance of a single-module P⁻¹ has been assumed.

There are two equivalent ways to see the ensuing degree-two boundary condition. Since pi is onto, (7.2) and surjectivity of Phi_J imply H^2(pi) is onto. Section 6 proves H^2(Q,I_env)=0, so H^2(Q,J_env)=0. This uses the actual class maps, not an abstract right-exactness oracle.

More explicitly, let v∈Z_Q^2(J_env) be any continuous two-cocycle. The low-degree construction (2.7), applied to J_env, gives

  v=kappa_(p')^J+D_J^1b,
  p'∈J_env, b∈C_Q^1(J_env).

Choose a coefficient lift p∈I_env with pi p=p'. kappa_p^I is an actual continuous two-cocycle by the low-degree chain calculation. Section 6 supplies its continuous I_env one-primitive theta^2kappa_p^I. Equation (7.1) then proves

  v=D_J^1[b+pi(theta^2kappa_p^I)].            (7.3)

Every cochain in (7.3) has the stated continuous type. This is an actual boundary witness, not just an H^2 caption. It establishes

  (E) every v∈Z_Q^2(J_env(M)) has a continuous primitive, for EVERY M∈A_Q.  (7.4)

The full natural degree-two hypothesis is thus supplied by the established low-degree result after the literal auxiliary fit, and the condition E is DERIVED here. The conditional higher lemma is not being applied with an unproved or finitely tested premise.

## 8. Continuous primitives in every degree at least three

We now use the established conditional higher lemma under the actually proved condition (7.4), and expose the construction to identify all continuous types. Prove simultaneously for ALL X∈A_Q by induction on n≥3 that every z∈Z_Q^n(X) is D_X^(n−1)y for a continuous y.

Fix X and use its actual I_env(X),J_env(X),iota_X,pi_X. Both auxiliary groups belong to A_Q by section 4. Define

  u=theta^n(iota_X o z)∈C_Q^(n−1)(I_env(X)).

The cochain iota_X o z is closed by full equivariance. Equation (6.2) gives

  D_I^(n−1)u=iota_X o z.

Let v=pi_X o u. Then v is a continuous (n−1)-cocycle with values in J_env(X), because pi_X iota_X=0.

If n=3, the actual boundary theorem (7.3) for J_env(X) gives w∈C_Q^1(J_env(X)) with D_J^1w=v. If n≥4, the induction hypothesis in degree n−1 applies to the full module J_env(X)∈A_Q and gives w∈C_Q^(n−2)(J_env(X)) with D_J^(n−2)w=v. The induction is well-founded because the degree decreases, and its universal coefficient quantifier includes each such auxiliary quotient; no boundedness or finite-module restriction is inserted.

Use the finite-image lifting construction of section 5 to choose W∈C_Q^(n−2)(I_env(X)) with pi_XW=w. Here n−2≥1. Then

  pi_X[u−D_I^(n−2)W]=v−D_J^(n−2)w=0.

The actual cochain kernel identity gives

  u−D_I^(n−2)W=iota_X o y,
  y=ev_1 o[u−D_I^(n−2)W]∈C_Q^(n−1)(X).

It is continuous into the original discrete X. Apply D and use D²=0 and equivariant postcomposition:

  iota_X o D_X^(n−1)y
       =D_I^(n−1)u−D_I^(n−1)D_I^(n−2)W
       =iota_X o z.

Injectivity of iota_X proves D_X^(n−1)y=z. This proves the universal higher primitive theorem and hence

  H^n_cont(Q,X)=0 for every X∈A_Q and n≥3.     (8.1)

The choices of the coefficient lift in (7.3), of w and of W are not asserted canonical, additive, natural or R-linear. Higher primitives are existence statements. Only the positive I_env contraction is a specified operator; no contraction or strict inverse on the original X-cochain complex follows. No spectral sequence, long exact sequence or higher-cohomology dimension theorem is used.

## 9. All-degree comparison and the full raw H^2 calibration

Take the original arbitrary M. The actual chain map j_M of the theorem has all-element identities (2.5) in degrees zero through two. In degrees at least three its chain identities hold because its source groups are zero. This is not a statement that the target cochains vanish.

In degree zero, (2.6) identifies H^0(j_M) with the identity on ker(T−1)∩ker(V−1). In degree one, evaluation of actual cocycles at h,q gives the inverse on cohomology by (2.6), and the source and target boundaries match exactly.

In degree two,

  H^2(K_M)=M/im d^1=M/mathfrak a_M.

The actual induced map is

  H^2(j_M)(t+mathfrak a_M)=[kappa_(P⁻¹t)]
             =barPhi_M(barP⁻¹(t+mathfrak a_M)).  (9.1)

P preserves mathfrak a_M in both directions by (2.9). Thus (9.1) is a bijection, with inverse

  (H^2(j_M))⁻¹=barP o barPhi_M⁻¹.            (9.2)

For surjectivity, if z has normalized coordinate p as in (2.7), take raw source class Pp. For injectivity, a boundary kappa_(P⁻¹t) has P⁻¹t∈mathfrak a_M by the actual boundary kernel theorem, hence t∈mathfrak a_M. Both statements use the full P and the proven quotient, not an arbitrary strict inverse of cochains.

On M/(T−1)M, and then on M/mathfrak a_M, barP=u_0 id. Only there can (9.1) be expressed as normalized Phi followed at its input by scalar u_0⁻¹. The source differential d^1, the one-cochain comparison and kappa_(P⁻¹t) on the full module retain their exact norms; neither P= u_0 on M nor V scalar is claimed.

For every n≥3, H^n(K_M)=0 because K_M^n=0. The target H^n_cont(Q,M)=0 by the actual continuous primitives (8.1), NOT by zeroing its cochain groups or assuming a final higher-vanishing predicate. Therefore H^n(j_M):0→0 is bijective. Together these prove H^n(j_M) bijective for ALL n≥0, that is, an additive quasi-isomorphism in the cohomological sense under the given data.

If both complexes are extended by formal zero groups in negative degrees, their negative cohomology is zero as well. This convention introduces no negative continuous-function space and gives no additional primitive claim.

## 10. Strict naturality and provided whole-ring linearity

For any actual additive full-Q-equivariant F:M→M', the low-degree local construction gives

  FT_x=T'_xF, FV_c=V'_cF,
  FP_c⁻¹=(P'_c)⁻¹F, FW_c=W'_cF,
  FB_b^V=B_(Fb)^(V'), FB_p^W=B_(Fp)^(W').

Consequently, on all raw terms,

  F f_(a,b)=f'_(Fa,Fb),
  F kappa_(P⁻¹t)=kappa'_((P')⁻¹Ft).

K(F) is the additive chain map F,F⊕F,F. Since pointwise postcomposition C_Q(F) commutes with signed D, these formulas and the zero-source higher components prove

  C_Q(F)j_M=j_(M')K(F)                       (10.1)

strictly in every degree. The now-established cohomology bijections commute with every such F. Naturality of a cohomology isomorphism is not naturality of the chosen higher boundary witnesses.

The envelope construction is compatible with coefficient maps too: I_env(F) is pointwise postcomposition and intertwines right translation; full equivariance gives I_env(F)iota_M=iota_(M')F and therefore an induced quotient map J_env(F). This does not make the selected finite-image lifts or higher primitives canonical.

No Q-module action is imposed on the raw complex terms, and an individual P⁻¹ on one M is not presumed a Q-equivariant coefficient-functor map. The actual identities above compare the operators under full-Q-equivariant coefficient maps.

If a ring R and whole left R-module structures with R-linear full Q-actions are given, canonical scalar and norm maps and the raw cochain formulas are R-linear by the low-degree theorem. Pointwise R-structure makes I_env a whole R-module; iota(M) is an R-submodule because R_x is R-linear; J_env has the quotient R-structure. Right translation, iota,pi andtheta are R-linear, but the finite-image choices of lifts and higher primitives are not asserted R-linear. The induced all-degree comparison maps are R-linear because the specified chain map j is R-linear. No finite orbit subgroup need be R-stable; no tensor, flatness, finite projectivity or perfection is assumed. Without a given R none is assigned.

## 11. Dependency map and scope of the assembled result

The low-degree input used here is the universal direct comparison with its actual full-action norms, continuous crossed maps, all-element signed chain squares, fresh H^0/H^1/H^2 completeness, exact boundary kernel and strict coefficient naturality. Its degree-two existence rests only on the two distinct direct normalized procyclic primitive theorems, applied to literal N and the given section C with their actual actions. The finite norm, crossed and scalar facts are local additive-orbit polynomial statements. The homomorphic section and group markings are given hypotheses, not conclusions about any arithmetic instance.

The higher input is the conditional coinduction lemma: unconditional uniform finite factorization, actual discrete envelopes, continuous cochain lifting and positive contraction, followed by universal higher induction conditional on the degree-two boundary property of J_env. Sections 4 and 7 supply its load-bearing membership and natural Phi premises at BOTH I_env and J_env, and establish that boundary property with actual continuous witnesses. Section 8 uses the now-discharged induction and exposes its types/signs. A conditional result has not been treated as an unconditional datum.

This is an all-degree comparison for the fixed given topological extension and every eligible full coefficient module. It does not give a strict inverse of the infinite continuous cochain complex, a chain contraction of M, a perfect H^1 cup pairing, a field or trace identification, a varying-ring tower or a derived-tensor/perfection statement. The target remains untruncated, full P and full actions remain unchanged, and higher primitives are only existence statements.
