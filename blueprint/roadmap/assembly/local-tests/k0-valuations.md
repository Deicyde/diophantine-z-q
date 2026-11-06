---
article_id: af_c0d526f1f4209b800feaa168
declaration: lemma
origin: background
---

# Valuations of the quadratic field

For a prime element $\pi$ of the principal ideal domain $\mathbb Z[s]$ let
$v_\pi:K_0\to\mathbb Z\cup\{\infty\}$ be the $\pi$-adic valuation, and let $p$ be the rational prime
in $\pi\mathbb Z[s]\cap\mathbb Z$ ("$\pi$ lies above $p$"). Then:

1. If $p$ is odd, every $\pi$ above $p$ has $v_\pi(p)=1$, and the primes above $p$ are $\pi$ and
   $\sigma(\pi)$ up to units (they are associate exactly when $p$ is inert). If $p=2$, the only
   prime above $2$ is $s$ up to units, and $v_s(2)=2$.
2. For $x\in\mathbb Q$, $v_\pi(x)=v_\pi(p)\,v_p(x)$.
3. For $x\in K_0$, $v_{\sigma(\pi)}(x)=v_\pi(\sigma(x))$.
4. Let $k\in\mathbb Z$ and $x\in K_0$ with $v_\pi(x)\ge k\,v_\pi(p)$ for every $\pi$ above $p$. If $p$ is
   odd then $v_p(\operatorname{Tr}x)\ge k$; if $p=2$ then $v_2(\operatorname{Tr}x)\ge k+1$.
5. In particular, if $v_\pi(x)\ge0$ for every $\pi$ above $p$, then $v_p(\operatorname{Tr}x)\ge0$.

**Proof sketch.** (1) The discriminant of $\mathbb Z[s]$ is $8$, so an odd $p$ is unramified:
either $x^2-2$ is irreducible modulo $p$ and $p$ stays prime, or $x^2-2\equiv(x-r)(x+r)$ with
$r\not\equiv-r$ and $p=\pm\pi\sigma(\pi)$ with $\pi=\gcd(p,s-r)$ and $\sigma(\pi)\sim\gcd(p,s+r)$ not associate;
$2=s^2$. (2) and (3) follow from (1) and the fact that $\sigma$ is a ring automorphism of
$\mathbb Z[s]$. (4) For odd $p$ the hypothesis says $x\in p^k\mathbb Z_{(p)}[s]$ (the semilocal
ring at $p$, a principal ideal ring whose maximal ideals are those of the primes above
$p$), so $x=p^k(a+bs)$ with $a,b\in\mathbb Z_{(p)}$ and $\operatorname{Tr}x=2p^ka$. For $p=2$ write $x=a+bs$;
then $v_s(x)=\min(2v_2(a),2v_2(b)+1)\ge2k$ gives $v_2(a)\ge k$, so $v_2(\operatorname{Tr}x)=v_2(2a)\ge k+1$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)
- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../../model/field/integers-pid.md)

## Sources

- [Lemma 11.1](../../../sources/assembly-locators.md#lemma-111)
- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
