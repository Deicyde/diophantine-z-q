---
article_id: af_d48ab6071f79b1fd166dfdfa
declaration: theorem
origin: background
---

# Primes above an odd prime

Let $p$ be an odd prime and $\mathbb Z[s]$, $s^2=2$, the ring of integers of $K_0$.

1. If $2$ is a square modulo $p$, choose $r\in\mathbb Z$ with $r^2\equiv2\pmod p$. The primes
   of $\mathbb Z[s]$ containing $p$ are exactly $\mathfrak p_+=(p,s-r)$ and $\mathfrak p_-=(p,s+r)$;
   they are distinct, $\mathbb Z[s]/\mathfrak p_\pm\cong\mathbb F_p$ via $a+bs\mapsto a\pm br\bmod p$,
   and $(p)=\mathfrak p_+\mathfrak p_-$.
2. If $2$ is not a square modulo $p$, then $(p)$ is a prime ideal of $\mathbb Z[s]$, and
   $\mathbb Z[s]/(p)$ is a field with $p^2$ elements.

In both cases there are at most two primes of $\mathbb Z[s]$ containing $p$, each has a
residue field with at most $p^2$ elements, each has $v_{\mathfrak p}(p)=1$, and the
conjugation $a+bs\mapsto a-bs$ permutes them (it swaps $\mathfrak p_+$ and $\mathfrak p_-$ and
fixes $(p)$).

**Proof sketch.** $\mathbb Z[s]\cong\mathbb Z[t]/(t^2-2)$, so
$\mathbb Z[s]/(p)\cong\mathbb F_p[t]/(t^2-2)$. If $t^2-2$ has the distinct roots $\pm r$ in
$\mathbb F_p$ ($p$ odd, $r\not\equiv0$), the Chinese remainder theorem gives
$\mathbb F_p\times\mathbb F_p$ with the two maximal ideals as stated, and
$\mathfrak p_+\mathfrak p_-=(p^2,p(s+r),p(s-r),2-r^2)$ is contained in $(p)$ (as
$2-r^2\in p\mathbb Z$) and contains $p^2$ and $p(s+r)-p(s-r)=2pr$, hence $p$ because
$\gcd(p,2r)=1$; so it equals $(p)$. If $t^2-2$ is irreducible, the quotient is a field with $p^2$ elements. Primes
containing $p$ correspond to maximal ideals of $\mathbb Z[s]/(p)$. Since $(p)$ is a product of
distinct primes, each appears with exponent one. Conjugation maps $s-r$ to $-(s+r)$.

This is standard (decomposition of primes in $\mathbb Q(\sqrt2)$, whose discriminant $8$ is
prime to $p$).

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [$\mathbb Z[\sqrt2]$ is a principal ideal domain](../../model/field/integers-pid.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
