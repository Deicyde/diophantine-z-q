---
article_id: af_939d2c81953715260cde59e4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Mult.formal_val_x_y, ZInQ.Mult.formalFilt, ZInQ.Mult.mem_formalNbhd_iff, ZInQ.Mult.zCoord_injOn, ZInQ.Mult.zsmul_mem_formalFilt
---

# The formal neighbourhood of $y^2=x^3+Ax$ and its filtration

Let $K$ be a field of characteristic $0$ with a discrete valuation $v$ normalized by
$v(K^\times)=\mathbb Z$ (for instance $K_0$ with $v_{\mathfrak p}$, or a completion of $K_0$).
Let $A\in K^\times$ with $v(A)\ge0$, and $W:y^2=x^3+Ax$ over $K$. Put
$$W_1(K)=\{O\}\cup\{(x,y)\in W(K):v(x)<0\},$$
and for $P=(x,y)\in W_1(K)$ put $z(P)=-x/y$, $w(P)=1/x$ and $\omega(P)=-1/y$, with
$z(O)=w(O)=\omega(O)=0$. Then:

1. for every affine $P=(x,y)\in W_1(K)$ there is an integer $N\ge1$ with $v(x)=-2N$ and
   $v(y)=-3N$; hence $y\ne0$, $v(z(P))=N$, $v(w(P))=2N=2v(z(P))$ and $v(\omega(P))=3N$;
2. for every integer $k\ge1$ the set $W_k(K)=\{P\in W_1(K):v(z(P))\ge k\}$ (containing $O$)
   is a subgroup of $W(K)$; in particular $W_1(K)$ is a subgroup;
3. $z$ is injective on $W_1(K)$;
4. for every $P\in W_1(K)$ and $n\in\mathbb Z$, $[n]P\in W_1(K)$ and $v(z([n]P))\ge v(z(P))$.

In part 1, $w=1/x$ is the manuscript's parameter; it differs from the auxiliary variable
$\omega=-1/y$ of Silverman, which is used only inside the proof. This is the elementary part of
Silverman VII.2.2 (there stated for a minimal equation over a complete field; only the
integrality of $A$ is used). The formal group law itself is a separate statement.

**Proof sketch.** (1) If $v(x)<0$ then $v(Ax)\ge v(x)>3v(x)$, so $2v(y)=v(x^3+Ax)=3v(x)$;
thus $v(x)$ is even, $v(x)=-2N$ with $N\ge1$, and $v(y)=-3N$.

*Coordinates.* For affine $P\in W_1(K)$, $x=z/\omega$ and $y=-1/\omega$, and dividing the
equation by $-y^3$ gives
$$\omega=z^3+Az\omega^2 .\tag{$*$}$$
Conversely a pair $(z,\omega)$ with $\omega\ne0$ satisfying $(*)$ is the image of the affine
point $(z/\omega,-1/\omega)$. If $v(z)\ge1$, $v(\omega)\ge1$ and $(z,\omega)$ satisfies $(*)$,
then $v(Az\omega^2)>v(\omega)$, so $v(\omega)=3v(z)$; in particular $\omega=0$ iff $z=0$. The
map $(x,y)\mapsto(z,\omega)$ is the projective change of coordinates
$[X:Y:Z]\mapsto[-X:-Z:Y]$, which sends $O=[0:1:0]$ to $(0,0)$ and lines to lines.

(2)-(3) Negation is $(x,y)\mapsto(x,-y)$, i.e. $(z,\omega)\mapsto(-z,-\omega)$, which preserves
$v(z)$. Let $P_1,P_2\in W_k(K)$ be affine with coordinates $(z_i,\omega_i)$, so $v(z_i)\ge k$ and
$v(\omega_i)=3v(z_i)\ge3k$. Subtracting the two instances of $(*)$ gives the identity
$$(\omega_2-\omega_1)\bigl(1-Az_1(\omega_1+\omega_2)\bigr)=(z_2-z_1)\bigl(z_1^2+z_1z_2+z_2^2+A\omega_2^2\bigr),$$
whose left factor $u=1-Az_1(\omega_1+\omega_2)$ is a unit. Hence $z_1=z_2$ forces
$\omega_1=\omega_2$, i.e. $P_1=P_2$; this is (3). Put
$$\lambda=\frac{z_1^2+z_1z_2+z_2^2+A\omega_2^2}{1-Az_1(\omega_1+\omega_2)},\qquad \nu=\omega_1-\lambda z_1 .$$
If $P_1\ne P_2$, $\omega=\lambda z+\nu$ is the line through them; if $P_1=P_2$ the same formula
gives the tangent, by implicit differentiation of $(*)$:
$\omega'(1-2Az\omega)=3z^2+A\omega^2$. In both cases $v(\lambda)\ge2k$ and $v(\nu)\ge3k$.
Substituting $\omega=\lambda z+\nu$ in $(*)$ gives the cubic
$$(1+A\lambda^2)z^3+2A\lambda\nu z^2+(A\nu^2-\lambda)z-\nu=0,$$
whose leading coefficient is a unit and whose roots, with multiplicity, are $z_1$, $z_2$ and
the $z$-coordinate $z_3$ of the third intersection point $Q$ of the line with $W$; by the
chord construction of the group law, $P_1+P_2=-Q$. By Vieta,
$$z_3=-z_1-z_2-\frac{2A\lambda\nu}{1+A\lambda^2},\qquad v(z_3)\ge k .$$
If $z_3=0$ then $\omega_3=\nu$ and $(*)$ gives $\nu=0$, so $Q=O$ and $P_1+P_2=O\in W_k(K)$.
Otherwise $\omega_3=\lambda z_3+\nu$ satisfies $v(\omega_3)\ge3k\ge1$, hence
$v(\omega_3)=3v(z_3)$ and $\omega_3\ne0$, so $Q=(z_3/\omega_3,-1/\omega_3)$ is affine with
$v(x(Q))=-2v(z_3)\le-2k$, and $P_1+P_2=-Q\in W_k(K)$ with $z(P_1+P_2)=-z_3$. Sums involving $O$
are trivial. (Alternatively, $z(P_1+P_2)=-z_3$ can be verified directly from the
Weierstrass addition formulas: the $(x,y)$-line $y=\ell x+m$ is $\omega=\lambda z+\nu$ with
$\lambda=-\ell/m$, $\nu=-1/m$ when $m\ne0$, and the case $m=0$ is the line through $O$.)

(4) By (2) with $k=v(z(P))$ (or $P=O$), $W_k(K)$ is a subgroup containing $P$, hence $[n]P$.

## Depends on

None.

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Silverman](../../../sources/multiplication-locators.md#silverman)
