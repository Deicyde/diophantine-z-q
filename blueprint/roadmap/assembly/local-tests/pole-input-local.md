---
article_id: af_796856202c2f11ddd07876f4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.poleInput_local
---

# Local conditions on the pole input

Let $n\in\mathbb Z\setminus\mathcal C$, let $\eta\in\{1,-1\}$ have the sign of $F(n)$, and put
$R_0=\eta\cdot2730^6\cdot F(n)$, a positive integer. Let $\kappa\ge1$ be such that for every prime element
$\pi$ of $\mathbb Z[s]$ dividing $R_0$,
$$[\kappa]P_0\in E_N(\pi)\qquad\text{for some }N\ge\max\bigl(1,v_\pi(F(n))\bigr).$$
Put $h=2\kappa$, $s_0=2\kappa n$, so that $H=[2\kappa]P_0$, $U=[2\kappa n]P_0$, $V_0=[\kappa]P_0$,
$V_1=[\kappa n]P_0$, and let $D_1,\dots,D_6$ and $C_j=D_j/F(n)$ be the six tests at $t=n$. Let
$q\in\mathbb Q$ with $v_p(q)\ge0$ for every prime $p\mid R_0$, and suppose that $a_0=1-R_0q^2$, $W$ and
$\Theta=\operatorname{Tr}(W^{-1})$ (formed with $R=R_0a_0^2$) are nonzero. Then $B=R/\Theta^2$ satisfies
$$v_2(B)\ge4,\qquad v_p(B)\ge6\ \ (p=3,5,7,13),\qquad\text{and the reduced denominator of }B\text{ is a square.}$$

**Proof sketch.** Let $S'$ be the set of primes dividing $R_0$; it contains $2,3,5,7,13$, and
$e_p=v_p(R_0)=6+v_p(F(n))$ for those five primes.

*The tests are small at $S'$.* Let $\pi$ divide $R_0$. All multiples of $[\kappa]P_0$ lie in
$E_N(\pi)$ and in $E_N(\sigma(\pi))$, and $\sigma(\pi)$ divides $R_0$ too. Hence
$v_\pi(D_1),v_\pi(D_2)\ge2N$ (for $w=1/x$), $v_\pi(D_3),v_\pi(D_4)\ge2N$ (at $\sigma(\pi)$), and, by the
multiplication statement applied to $Q=[2\kappa]P_0$ at $\pi$ and to $Q=[\kappa]P_0$ at $\sigma(\pi)$,
$v_\pi(D_5),v_\pi(D_6)\ge4N$. So $v_\pi(D_j)\ge v_\pi(F(n))$ for all $j$.

*$W\equiv1$ and $\Theta\equiv2$.* At $\pi\mid p\in S'$, $q$ is integral and $v_\pi(R_0q^2)\ge1$, so $a_0$ is a
unit and $v_\pi(RC_j^2)=v_\pi(R_0)+2(v_\pi(D_j)-v_\pi(F(n)))\ge v_\pi(R_0)$. Hence
$v_\pi(W-1)\ge v_\pi(R_0)$, $W$ is a unit and $v_\pi(W^{-1}-1)\ge v_\pi(R_0)=e_pv_\pi(p)$. The trace
statement gives $v_p(\Theta-2)\ge e_p$ for odd $p$, so $\Theta$ is a $p$-unit, and
$v_2(\Theta-2)\ge e_2+1\ge7$, so $v_2(\Theta)=1$.

*Valuations of $B$.* For odd $p\in S'$, $v_p(B)=e_p\ge1$, and $e_p\ge6$ for $p=3,5,7,13$. At $2$,
$v_2(B)=e_2-2=4+v_2(F(n))\ge4$. For $p\notin S'$, $v_p(R_0)=0$, so $v_p(B)=2v_p(a_0)-2v_p(\Theta)$ is
even. Thus every prime of the reduced denominator of $B$ lies outside $S'$ and occurs to an
even power.

## Depends on

- [The six local tests](../value-templates/six-local-tests.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../../multiplication/local/formal-group.md)
- [Multiplication in a formal neighbourhood](formal-multiplication.md)

## Proof depends on

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)
- [Valuation and trace at the prime $(s)$](dyadic-trace.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
