---
article_id: af_6e5ed9f2cb0e8b8174b6d44f
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.smallHeight_search
---

# The finite search for small points on $C$

Let $f(x)=x^3-\delta^2x$ with $\delta^2=11-6s$. Let $\mathcal Q$ be the set of integer triples
$(a,b,c)$ with $1\le a\le81$, $|b|\le162$, $|c|\le81$, $\gcd(a,b,c)=1$ and $b^2-4ac=2k^2$ for an
integer $1\le k\le162$; let $\mathcal X_2$ be the set of the numbers
$x=\frac{-b\pm ks}{2a}\in K_0$ for $(a,b,c)\in\mathcal Q$ and both signs; and let $\mathcal X_1$ be
the set of rationals $p/q$ with $\gcd(p,q)=1$, $|p|\le9$, $1\le q\le9$. Then:

1. $|\mathcal Q|=7004$, the roots counted with their sign number $14008$, and
   $|\mathcal X_1|=111$;
2. for $x\in\mathcal X_1\cup\mathcal X_2$, $f(x)$ is a square in $K_0$ if and only if
   $$x\in\Bigl\{0,\ \delta,\ -\delta,\ 1+s,\ 23-17s,\ 2+4s,\ \tfrac{5-4s}{2}\Bigr\}.$$

Each membership test is the exact square test applied to the two rational components of
$f(x)$. This is a finite computation over explicit finite sets.

**Proof sketch.** Enumerate the box: for each $(a,b,c)$ check primitivity and whether
$(b^2-4ac)/2$ is a positive perfect square $k^2$ with $k\le162$; for each resulting $x$ and each
rational candidate compute the components of $f(x)$ exactly and run the square test. An
independent replay of exactly this computation gives the stated counts and survivors.

## Depends on

- [An exact square test in $K_0$](square-test.md)
- [The change of variables to $C$](../descent/coordinate-change.md)

## Sources

- [Finite search](../../../sources/model-locators.md#finite-search)
