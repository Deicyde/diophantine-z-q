---
article_id: af_a8b5a44c51df4e746696c7fa
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.exists_mk0_coprime, ZInQ.RouteK.Redei.not_dvd_absNorm_of_sup_span_eq_top
---

# Every class has a representative of norm prime to $q$

Let $n\ge1$, $\mathcal O$ the ring of integers of $\mathbb Q(\sqrt{-n})$ and $q$ a prime. Every
ideal class of $\mathcal O$ contains a nonzero ideal $I$ with $q\nmid N(I)$. Along the way, an
ideal $I$ with $I+q\mathcal O=\mathcal O$ satisfies $q\nmid N(I)$.

**Proof sketch.** Let $c$ be the class, and take a nonzero ideal $J$ in $c^{-1}$. Since
$\mathcal O$ is a Dedekind domain and $J\cdot q\mathcal O\subseteq J$ is nonzero, there is $a\in J$
with $J\cdot q\mathcal O+(a)=J$. As $a\in J$, write $(a)=JM$. Then
$J(q\mathcal O+M)=J=J\mathcal O$, and cancelling $J$ gives $M+q\mathcal O=\mathcal O$. Also
$M\ne0$, since otherwise $q\mathcal O=\mathcal O$ and $q$ would divide $1$ in $\mathcal O$, hence
in $\mathbb Z$. From $[J][M]=[(a)]=1$, $[M]=c$. Finally, if $q$ divided $N(M)$, some maximal
ideal over $q$ would divide $M$; it would contain both $M$ and $q$, hence
$M+q\mathcal O=\mathcal O$, which is impossible for a maximal ideal.

## Depends on

- [The genus class number](../genus-class-number.md)

## Proof depends on

- [Rational integers in the ring of integers](../field/rational-integers.md)
- [Split, inert and ramified primes](../field/prime-trichotomy.md)

## Sources

- [Step 4: genus characters](../../../sources/redei-locators.md#step-4-genus-characters)
