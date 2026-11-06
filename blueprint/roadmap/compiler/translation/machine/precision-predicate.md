---
article_id: af_34dc554711ec767ad0b6bf8a
declaration: def
origin: cited
---

# The precision predicate

*Signed encoding.* $\operatorname{enc}:\mathbb Z\to\mathbb N$ is $\operatorname{enc}(n)=2n$ for $n\ge0$ and
$\operatorname{enc}(n)=-2n-1$ for $n<0$; it is a bijection, with inverse $c\mapsto c/2$ for even $c$
and $c\mapsto-(c+1)/2$ for odd $c$.

*Constants.* $\mathcal C=\{0,-15,-20,-24,-30,-60\}$ and $F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$.
With $F_0=324!$, $D=F_0\,3^{256F_0^4}$, $G_0=116064000000$, $E_0=10(DG_0)^2$,
$B_{\rm cm}=D^2\,3^{21000D^2}+1$ and $C_{\rm cm}=2B_{\rm cm}+4096(1028+5D+84000D^2)$, put
$$A^{(0)}_{\rm ht}=H_6(S_{\rm ht})=H_6(S_{\rm ht};D)=2\cdot10^{13}\max\bigl(1,\ C_{\rm cm},\ D^{17DE_0}\bigr)\in\mathbb N,$$
where $S_{\rm ht}$ is the set of primes at most $324$, so that $\max(D,\max S_{\rm ht},10^{12})=D$
and $Q_D^{17}=D^{17DE_0}$. This integer is astronomically large; it is used only through its
defining expression.

*Points.* A point $Q\in E(K_0)$ is *nondegenerate* when $Q=(x,y)$ is affine with $x\ne0$ and
$y\ne0$; then $z(Q)=-x/y\in K_0^\times$.

*The predicate.* For $\mathbf c=(c_0,\dots,c_4)\in\mathbb N^5$ let
$(n,\kappa,a,l,j)=(\operatorname{enc}^{-1}c_0,\dots,\operatorname{enc}^{-1}c_4)$. Then
$\mathrm{accepts\_naturals}(\mathbf c)$ holds exactly when

1. $n\notin\mathcal C$, $\kappa\ne0$, $a\ge1$, $l\ge1$ and $j=na$;
2. $[l]P_0$, $[a]P_0$ and $[j]P_0$ are nondegenerate;
3. writing $z([l]P_0)=u_l+v_ls$ with $u_l,v_l\in\mathbb Q$, $\epsilon_l=|u_l|+|v_l|$ and
   $r(a,j)=\tfrac12\operatorname{Tr}_{K_0/\mathbb Q}\bigl(z([j]P_0)/z([a]P_0)\bigr)\in\mathbb Q$, both strict tests
   hold:
   $$|r(a,j)-n|<\epsilon_l,\qquad 4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}} .$$

Condition 2 makes the predicate total without any input about $P_0$; by the nondegeneracy of
nonzero multiples of $P_0$ it follows from condition 1, so the predicate is the manuscript's.
Both tests compare exactly computable rationals. Writing $\epsilon_l=U/V$ with natural
$U,V\ge1$, the second test is equivalent to $4^{A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}\le\lfloor(V-1)/(4U)\rfloor$.
This is a definition.

## Depends on

- [The six-contact height estimate](../../../main/six-contact-estimate.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Sources

- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
- [Section 4 height constants](../../../../sources/compiler-translation-locators.md#section-4-height-constants)
- [Section 11 precision contract](../../../../sources/compiler-translation-locators.md#section-11-precision-contract)
