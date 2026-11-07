---
article_id: af_5ab0ee2cb4c01274f034ffe1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.exists_formal_multiple, ZInQ.Size.leastFormalMultiple_bounds, ZInQ.Size.leastFormalMultiple_formalCondition, ZInQ.Size.M0_bounds
---

# A successful formal multiple

For a point $Q\in E(K_0)$ let $\xi(Q)=1/x(Q)$ if $Q\ne O$ and $x(Q)\ne0$, and $\xi(Q)=0$
otherwise. For every integer $N\ge1$ there is an integer $m$ with $1\le m\le N^{10}$ such
that the normalized representation $\xi([m]P_0)=(a+bs)/c$ ($a,b,c\in\mathbb Z$, $c>0$,
$\gcd(a,b,c)=1$) satisfies
$$N^4\mid a,\qquad N^4\mid b,\qquad \gcd(c,N)=1 .$$
Consequently $1\le\mathrm{LFM}(N)\le N^{10}$ and $\mathrm{LFM}(N)$ itself satisfies these three
conditions. In particular, whenever $N_s\ge1$ (which holds under the catalogue bound, and also by
Dirichlet's theorem, since every catalogue entry is then a prime), $1\le M_0\le N_s^{10}$ and $M_0$
is a successful index. The positivity of $N_s$ is needed: for $N=0$ the conditions force
$a=b=0$ and $c=1$, that is $\xi([m]P_0)=0$.

**Proof sketch.** Take $m_0$ from the reduction orders and $m=N^4m_0$, so $1\le m\le N^{10}$.
If $[m]P_0=O$ or $x([m]P_0)=0$, then $\xi=0=(0+0s)/1$ and the conditions hold. Otherwise
write $u=\xi([m]P_0)=u_0+u_1s$ with $u_0,u_1\in\mathbb Q$.

*Odd $p\mid N$.* At every prime $\mathfrak p\ni p$, $[m_0]P_0\in E_1(\mathfrak p)=W_1$ and
$v_{\mathfrak p}(N^4)=4v_p(N)$, so multiplication in the formal neighbourhood (item 3) gives $[m]P_0\in W_{1+4v_p(N)}$, that is
$v_{\mathfrak p}(u)=-v_{\mathfrak p}(x)\ge2+8v_p(N)$. By the extraction at odd primes,
$v_p(u_0),v_p(u_1)\ge2+8v_p(N)\ge4v_p(N)$.

*$p=2$, if $N$ is even.* $P_0\in W_3$ at $(s)$, and $v_s(m)=2v_2(m)\ge8v_2(N)$, so
$[m]P_0\in W_{3+8v_2(N)}$ and $v_s(u)\ge6+16v_2(N)$. By
$v_s(u_0+u_1s)=\min(2v_2(u_0),2v_2(u_1)+1)$, $v_2(u_0)\ge3+8v_2(N)$ and
$v_2(u_1)\ge3+8v_2(N)$, both at least $4v_2(N)$.

*Normalization.* The normalized representation has $c=\operatorname{lcm}(\operatorname{den}u_0,\operatorname{den}u_1)$,
$a=u_0c$, $b=u_1c$. For $p\mid N$, $v_p(u_i)\ge0$, so $p\nmid c$; thus $\gcd(c,N)=1$ and
$v_p(a)=v_p(u_0)\ge4v_p(N)$, $v_p(b)=v_p(u_1)\ge4v_p(N)$ for every $p\mid N$, i.e.
$N^4\mid a$ and $N^4\mid b$. The set of successful indices is therefore nonempty, so its least
element $\mathrm{LFM}(N)$ is successful and at most $m$.

No property of $P_0$ beyond those cited is needed; in particular the argument does not use
that $P_0$ has infinite order (the conventions for $\xi$ cover the identity). The manuscript
loses up to three units of $v_s$ when extracting $u_0,u_1$; the exact valuation formula at
$(s)$ avoids this.

## Depends on

- [The least formal multiple](../../syntax/constants/least-formal-multiple.md)
- [The point $P_0$](../../model/field/generator-point.md)

## Proof depends on

- [Reduction orders of $P_0$](reduction-orders.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../../multiplication/local/formal-group.md)
- [Multiplication in a formal neighbourhood](../../assembly/local-tests/formal-multiplication.md)
- [The generator lies in the dyadic formal group](../../multiplication/local/dyadic-generator.md)
- [Rational coordinates at odd primes](odd-coefficient-extraction.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Section 2.2 catalogue and formal multiple](../../../sources/size-locators.md#section-22-catalogue-and-formal-multiple)
