---
article_id: af_6118f908eb3b95de3c300ea7
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.primeR_split, ZInQ.Mult.primeP_inert, ZInQ.Mult.vp_ratCast, ZInQ.Mult.vp_star, ZInQ.Mult.vp_trace_ge
---

# The primes of $\mathbb Z[\sqrt2]$ above an odd prime

Let $p$ be an odd prime and $\sigma$ the conjugation $s\mapsto-s$ of $K_0$.

1. If $2$ is a square modulo $p$, choose $r\in\mathbb Z$ with $r^2\equiv2\pmod p$. Then
   $\mathfrak p_r=(p,s-r)$ and $\mathfrak p_{-r}=(p,s+r)$ are distinct prime ideals of
   $\mathbb Z[s]$, $a+bs\mapsto(a+br)\bmod p$ induces $\mathbb Z[s]/\mathfrak p_r\cong\mathbb F_p$,
   $p\mathbb Z[s]=\mathfrak p_r\mathfrak p_{-r}$ and $\sigma(\mathfrak p_r)=\mathfrak p_{-r}$.
   Otherwise $p\mathbb Z[s]$ is prime, with residue field of $p^2$ elements, and
   $\sigma(p\mathbb Z[s])=p\mathbb Z[s]$. In both cases these are all the prime ideals of
   $\mathbb Z[s]$ containing $p$.
2. For a prime $\mathfrak p\ni p$ let $v_{\mathfrak p}$ be the normalized valuation of $K_0$
   ($v_{\mathfrak p}(K_0^\times)=\mathbb Z$, $v_{\mathfrak p}(0)=+\infty$). Then $p$ is
   unramified: $v_{\mathfrak p}(q)=v_p(q)$ for every $q\in\mathbb Q$.
3. $v_{\sigma\mathfrak p}(y)=v_{\mathfrak p}(\sigma y)$ for every $y\in K_0$.
4. For $y\in K_0$ and $m\in\mathbb Z$, if $v_{\mathfrak p}(y)\ge m$ and
   $v_{\sigma\mathfrak p}(y)\ge m$, then $v_p(\operatorname{Tr}y)\ge m$, where
   $\operatorname{Tr}y=y+\sigma y\in\mathbb Q$.

At the prime $2$ the corresponding facts are those of the prime $(s)$.

**Proof sketch.** (1) is Dedekind-Kummer for $\mathbb Z[s]=\mathbb Z[X]/(X^2-2)$, whose
discriminant $8$ is prime to $p$: $X^2-2$ is separable modulo $p$ and factors as
$(X-r)(X+r)$ or is irreducible. (2) $p\mathbb Z[s]$ is a product of distinct primes, so
$v_{\mathfrak p}(p)=1$. (3) $\sigma$ is a ring automorphism of $\mathbb Z[s]$ mapping
$\mathfrak p$ to $\sigma\mathfrak p$. (4) $\operatorname{Tr}y=y+\sigma y$ and
$v_{\mathfrak p}(\sigma y)=v_{\sigma\mathfrak p}(y)\ge m$; the ultrametric inequality gives
$v_{\mathfrak p}(\operatorname{Tr}y)\ge m$, and $v_{\mathfrak p}=v_p$ on $\mathbb Q$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../../model/field/integers-pid.md)

## Sources

- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
