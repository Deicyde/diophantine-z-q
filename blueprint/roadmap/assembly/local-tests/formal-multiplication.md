---
article_id: af_fdd11da248e86a22d5f24b93
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Assembly.val_zCoord_add_sub, ZInQ.Assembly.val_zCoord_zsmul_sub, ZInQ.Assembly.zsmul_mem_formalFilt_succ, ZInQ.Assembly.zsmul_mem_formalFilt_add_val, ZInQ.Assembly.zCoord_zsmul_eq_mul_unit
---

# Multiplication in a formal neighbourhood

Let $K$ be a field of characteristic $0$ with a discrete valuation $v$, $v(K^\times)=\mathbb Z$,
whose residue field has characteristic $p>0$. Let $A\in K^\times$ with $v(A)\ge0$,
$W:y^2=x^3+Ax$, and let $W_k(K)$ and $z$ be as in the formal neighbourhood statement: $W_k(K)$ is
the subgroup of the points with $v(z)\ge k$, that is $v(x)\le-2k$, together with $O$. Then:

1. for $k\ge1$ and $P,Q\in W_k(K)$,
   $$v\bigl(z(P+Q)-z(P)-z(Q)\bigr)\ge5k ;$$
2. for every affine $Q\in W_1(K)$, with $k=v(z(Q))$, and every $n\in\mathbb Z$,
   $v\bigl(z([n]Q)-n\,z(Q)\bigr)\ge5k$, hence $v\bigl(z([n]Q)/z(Q)-n\bigr)\ge4k$;
3. $[p]W_k(K)\subseteq W_{k+1}(K)$ for every $k\ge1$; and if $v(p)\le4$, then
   $[n]W_k(K)\subseteq W_{k+v(n)}(K)$ for every nonzero $n\in\mathbb Z$ and every $k\ge1$;
4. if $p$ is odd and $v(p)=1$, then for every affine $Q\in W_1(K)$, with $k=v(z(Q))$, and every
   nonzero $m\in\mathbb Z$, the point $[m]Q$ is affine, $v(z([m]Q))=k+v_p(m)$, and
   $$z([m]Q)=m\,z(Q)\,u_m\qquad\text{with }v(u_m-1)\ge1 .$$

On $K_0$, for a prime element $\pi$ of $\mathbb Z[s]$, write $E_k(\pi)$ for the subgroup $W_k(K_0)$
of $E$ at $v=v_\pi$, and $\nu_\pi(P)=v_\pi(z(P))$ for affine $P\in E_1(\pi)$. The hypotheses hold at
every $\pi$, including $s$ and $d$, because $A=-d^2$ is integral everywhere; $v_\pi(p)=1$ at a
prime above an odd prime $p$, and $v_s(2)=2$.

Item 4 is the content of "$\log([m]Q)=m\log(Q)$ and $\log$ is an isometry with
$\log(Q)=z(Q)(1+e_Q)$, $v(e_Q)\ge1$" used in the manuscript, in the form actually needed. Item 3
is the elementary form of the logarithm isometry: the manuscript argues at $(s)$ with
$v_s(z([2]Q))=v_s(z(Q))+2$ for $v_s(z(Q))\ge3$, and the inequality $\ge$ given by item 3 is all
that is used.

**Proof sketch.** (1) Use the coordinates $z$ and $\omega=-1/y$ of the formal neighbourhood
statement. For affine $P_1,P_2\in W_k(K)$ with $P_2\ne-P_1$, its chord construction gives the line
$\omega=\lambda z+\nu$ through them (the tangent if $P_1=P_2$), with $v(\lambda)\ge2k$ and
$v(\nu)\ge3k$, and by Vieta on the cubic $(1+A\lambda^2)z^3+2A\lambda\nu z^2+(A\nu^2-\lambda)z-\nu=0$,
$$z(P_1+P_2)=z(P_1)+z(P_2)+\frac{2A\lambda\nu}{1+A\lambda^2},$$
where the last term has valuation at least $5k$ because $1+A\lambda^2$ is a unit. Sums involving
$O$, and $P_2=-P_1$, are immediate since $z(-P)=-z(P)$.

(2) The multiples $[j]Q$ lie in the subgroup $W_k(K)$. By (1),
$z([j+1]Q)=z([j]Q)+z(Q)+e_j$ with $v(e_j)\ge5k$; summing gives the claim for $n\ge0$, and
$z(-P)=-z(P)$ gives $n<0$. Divide by $z(Q)$, which has valuation $k$.

(3) Let $Q\in W_k(K)$ be affine with $v(z(Q))=k'\ge k$. By (2),
$v(z([p]Q))\ge\min(5k',k'+v(p))$, which is at least $k'+1$, and equals $k'+v(p)$ when
$v(p)\le4$; so $[p]Q\in W_{k+1}(K)$, and $[p]Q\in W_{k+v(p)}(K)$ when $v(p)\le4$. Iterate for
powers of $p$, and note that $[n']W_k(K)\subseteq W_k(K)$ for $n'$ prime to $p$.

(4) Now $v(p)=1$. For $p\nmid m'$: by (2), $z([m']Q)=m'z(Q)(1+\epsilon)$ with
$v(\epsilon)\ge4k\ge1$, so $v(z([m']Q))=k$. For $p$: $z([p]Q)=p\,z(Q)(1+\epsilon)$ with
$v(\epsilon)\ge5k-(k+1)\ge3$, so $v(z([p]Q))=k+1$. Write $m=p^em'$ and compose, applying these to
$[p^i]Q$ (of valuation $k+i$) and then to $[p^e]Q$; the units multiply and stay $\equiv1$. In
particular $z([m]Q)\ne0$, so $[m]Q\ne O$.

## Depends on

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../../multiplication/local/formal-group.md)
- [The generator curve $E$](../../model/field/generator-curve.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Proof depends on

- [The chord estimate in a formal neighbourhood](../../multiplication/local/chord-estimate.md)

## Sources

- [Section 6 formal conventions](../../../sources/assembly-locators.md#section-6-formal-conventions)
- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
- [Silverman](../../../sources/assembly-locators.md#silverman)
- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
