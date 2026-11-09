---
article_id: af_d44ff761404b44e08d384f68
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.test_dvd
---

# Divisibility from the six local tests

Let $n,\kappa\in\mathbb Z$ and $t\in\mathbb Q$. If $\operatorname{Test}(n,\kappa,t)$ holds, then
$$M_{S_{\rm ht}}(t)\ \big|\ \kappa F(n),$$
where $M_{S_{\rm ht}}(t)$ is the product of the primes $p>324$ for which $v_p(t-c)$ is positive and
odd for some $c\in\mathcal C$. No unit assumption on $\kappa$ is used, and no hypothesis is
needed.

**Proof sketch.** Fix the data $h,s_0,\eta,q$ of the test. Since $M_{S_{\rm ht}}(t)$ is squarefree,
it suffices to show $p\mid\kappa F(n)$ for every prime $p>324$ with $\delta=v_p(t-c)>0$ odd for some
$c\in\mathcal C$. For $c'\ne c$ in $\mathcal C$, $0<|c-c'|\le60<p$, so $v_p(t-c')=0$; hence $v_p(F(t))=\delta$,
and $t$ is $p$-integral. The primes above $p$ have $v_\pi(p)=1$, and $v_\pi$ restricts to $v_p$ on
$\mathbb Q$.

*Valuation of $R$.* $\eta$ and $2730^6$ are $p$-units, so $v_p(R_0q^2)=\delta+2v_p(q)$ when $q\ne0$.
Put $b=v_p(a_0)$. If $q=0$ then $b=0$; otherwise $\delta+2v_p(q)$ is odd, hence nonzero, and
$b=\min(0,\delta+2v_p(q))\le0$. So $\alpha=v_p(R)=\delta+2b$ is odd.

*Valuation of $W$.* At each prime $\pi$ above $p$, $v_\pi(RC_j^2)=\alpha+2(v_\pi(D_j)-\delta)$ is odd,
hence nonzero, so $v_\pi(1+RC_j^2)=\min\bigl(0,\alpha+2(v_\pi(D_j)-\delta)\bigr)$ (this is $0$ if
$D_j=0$). Let $\lambda=\max_{\pi\mid p}v_\pi(W)\le0$. Since $v_\pi(W^{-1})\ge-\lambda$ at every $\pi$ above $p$,
the trace statement gives $v_p(\Theta)\ge-\lambda\ge0$.

*The pole input.* $B_{\rm pole}=R/\Theta^2\ne0$ has $v_p(B_{\rm pole})=\alpha-2v_p(\Theta)$, which is odd;
since $\Phi(B_{\rm pole})$ and $p\notin\{2,3,5,7,13\}$, the one-sided pole obstruction says it is not
negative, so it is positive. Hence $\alpha>2v_p(\Theta)\ge-2\lambda\ge0$: $\alpha>0$ and $\lambda>-\alpha/2$.

*All six tests are small at one prime.* Take $\pi$ above $p$ with $v_\pi(W)=\lambda$. The six terms
$\min(0,\alpha+2(v_\pi(D_j)-\delta))$ are $\le0$ and sum to $\lambda$, so each is $\ge\lambda>-\alpha/2$; hence
$v_\pi(D_j)>\delta-3\alpha/4=\delta/4-3b/2>0$, so $v_\pi(D_j)\ge1$ for $j=1,\dots,6$. Let $\pi'=\sigma(\pi)$, so
$v_\pi(\sigma(x))=v_{\pi'}(x)$.

*Formal groups.* $v_\pi(D_1)\ge1$ and $v_\pi(D_2)\ge1$ put $H\ne O$ and $U$ in $E_1(\pi)$;
$v_\pi(D_3)\ge1$ and $v_\pi(D_4)\ge1$ put $V_0\ne O$ and $V_1$ in $E_1(\pi')$. The fifth test makes
$z(U)/z(H)$ integral at $\pi$ and congruent to $t$ modulo $\pi$. Let $g=\gcd(h,s_0)>0$ and
$Q=[g]P_0$. The set of $m$ with $[m]P_0\in E_1(\pi)$ is a subgroup of $\mathbb Z$ containing $h$ and
$s_0$, so $Q\in E_1(\pi)$, and $Q\ne O$ because $H=[h/g]Q\ne O$. By the multiplication statement
($p$ odd), $z(H)=(h/g)z(Q)u$ and $z(U)=(s_0/g)z(Q)u'$ with $u,u'\equiv1\pmod\pi$ (for $s_0=0$ take
$u'=1$). Hence $s_0/h=(z(U)/z(H))(u/u')$ is $\pi$-integral and congruent to $t$, so
$v_p(s_0/h-t)\ge1$ and, $h$ being an integer, $s_0\equiv th\pmod p$ in $\mathbb Z_{(p)}$. The same
argument at $\pi'$ with $V_0=[h-\kappa]P_0$, $V_1=[s_0-\kappa n]P_0$ and the sixth test gives
$s_0-\kappa n\equiv t(h-\kappa)\pmod p$. Subtracting, $v_p(\kappa(t-n))\ge1$; since $v_p(t-c)\ge1$,
$p\mid\kappa(n-c)$, and $n-c$ divides $F(n)$, so $p\mid\kappa F(n)$.

## Depends on

- [The six local tests](../value-templates/six-local-tests.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)

## Proof depends on

- [The one-sided pole obstruction](../../multiplication/pole-obstruction.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../../multiplication/local/formal-group.md)
- [Multiplication in a formal neighbourhood](formal-multiplication.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
