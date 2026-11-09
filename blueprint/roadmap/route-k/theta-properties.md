---
article_id: af_086a0d5e5de6965f66691b9e
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.theta_props, ZInQ.RouteK.theta1, ZInQ.RouteK.theta2, ZInQ.RouteK.theta2_isCoprime, ZInQ.RouteK.theta3, ZInQ.RouteK.theta4
---

# The properties (θ1)–(θ4)

Let $B$ be admissible, $m$ a signed divisor of $2730$, $\beta=\mathrm{sqf}(mB)$ and
$\theta=\mathrm{sqf}(m(m-B))$. Then:

- (θ1) $\theta>0$, $\theta\equiv1\pmod8$ and $\gcd(\theta,2730)=1$;
- (θ2) no prime divides both $\beta$ and $\theta$;
- (θ3) $(\beta/\ell)=1$ for every prime $\ell\mid\theta$;
- (θ4) $(\theta/p)=1$ for every odd prime $p\mid\beta$.

Property (θ4) also holds at $p=2$, since $\theta$ is odd.

**Proof sketch.** Write $B=a/k^2$ in lowest terms, so $0<2a<k^2$ and, for $p\in S_0$, $p\nmid k$
and $p^4\mid a$. With $M=mk$ there are nonzero integers $s,c$ with
$$ma=\beta s^2,\qquad\theta c^2=M^2-ma,$$
the integer form of $\theta c^2=1-\beta t^2$, $\beta t^2=B/m$. The local computation is one
lemma: if $\theta c^2=(p^eM_1)^2-X$ with $\theta$ squarefree, $p\nmid M_1$ and
$p^{2e+j}\mid X$ for some $j\ge1$, then $p\nmid\theta$ and $\theta c_1^2\equiv M_1^2\pmod{p^j}$
for some $c_1$ prime to $p$. At $p\in S_0$ it applies with $j=3$ ($p^4\mid a$, and $p^2\nmid m$),
which gives $p\nmid\theta$ and, at $p=2$, $\theta\equiv1\pmod8$, because odd squares are
$\equiv1\pmod8$; and $\theta>0$ because $M^2-ma=m^2k^2(1-B/m)$ with $|B/m|\le B<1/2$. This is
(θ1). At a prime $p\mid\beta$ outside $S_0$: $p\mid ma$ and $p\nmid m$, so $p\mid a$ and $p\nmid k$;
the lemma applies with $e=0$, $j=1$, so $p\nmid\theta$ and $\theta$ is a nonzero square modulo
$p$; at a prime of $\beta$ in $S_0$ the first case gives the same. This gives (θ2) and (θ4). At a prime $\ell\mid\theta$: $\ell\notin S_0$ by (θ1), so
$\ell\nmid m$; $\ell\nmid k$, since otherwise $\ell\mid M^2-\theta c^2=ma$ would give $\ell\mid a$;
hence $\beta s^2=ma\equiv M^2\not\equiv0\pmod\ell$, and $\beta$ is a nonzero square modulo
$\ell$, which is (θ3).

## Depends on

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)

## Sources

- [Inputs and the properties of theta](../../sources/route-k-locators.md#inputs-and-the-properties-of-theta)
