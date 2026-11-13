---
article_id: af_b0daad8c7392a63e44c272db
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Assembly.Test, ZInQ.Assembly.test_iff
---

# The six local tests

For $n,\kappa\in\mathbb Z$ and $t\in\mathbb Q$, the relation $\operatorname{Test}(n,\kappa,t)$ holds when
$\kappa\ne0$, $t\notin\mathcal C$, and there are integers $h,s_0$ and rationals $\eta,q$ with the
following properties. Put
$$H=[h]P_0,\qquad U=[s_0]P_0,\qquad V_0=[h-\kappa]P_0,\qquad V_1=[s_0-\kappa n]P_0,$$
and require $h\ne0$ and $h\ne\kappa$ (that is, $H\ne O$ and $V_0\ne O$). With $z(Q)=-x/y$ and
$w(Q)=1/x$ for an affine point $Q=(x,y)$ with $xy\ne0$, $z(O)=w(O)=0$, and $\sigma$ the
conjugation of $K_0$, define the six tests
$$D_1=w(H),\quad D_2=w(U),\quad D_3=\sigma\bigl(w(V_0)\bigr),\quad D_4=\sigma\bigl(w(V_1)\bigr),$$
$$D_5=\frac{z(U)}{z(H)}-t,\qquad D_6=\sigma\Bigl(\frac{z(V_1)}{z(V_0)}\Bigr)-t$$
in $K_0$ (the denominators are nonzero because $H,V_0$ are nonzero multiples of $P_0$), and
$$R_0=\eta\cdot2730^6\cdot F(t),\quad a_0=1-R_0q^2,\quad R=R_0a_0^2,\quad C_j=\frac{D_j}{F(t)},\quad
W=\prod_{j=1}^6\bigl(1+RC_j^2\bigr)\in K_0 .$$
The conditions are
$$\eta^2=1,\qquad a_0\ne0,\qquad W\ne0,\qquad \Theta:=\operatorname{Tr}(W^{-1})\ne0,\qquad
\Phi\bigl(R/\Theta^2\bigr).$$
Here $2730^6=413976684737889000000$, $F(t)\ne0$ because $t\notin\mathcal C$, and $\Phi$ is rational
solubility of the pole polynomial. There is one common denominator $F(t)$, one product $W$,
one trace and one pole instance. Write $B_{\rm pole}=R/\Theta^2$.

The manuscript states $\operatorname{Test}(N,\mathcal K,t)$ for codes $N=\iota(n)$, $\mathcal K=\iota(\kappa)$,
with $H=\iota(h)$, $U=\iota(s_0)$ and the code of $\kappa n$ formed by multiplication; this
article states it on the indices, and the semantics of the value-test template connects
the two.

This is a definition.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)
- [Pole completeness](../../main/pole-completeness.md)
- [Point codes](../../model/point-codes.md)

## Sources

- [Section 11.2 six local tests](../../../sources/assembly-locators.md#section-112-six-local-tests)
