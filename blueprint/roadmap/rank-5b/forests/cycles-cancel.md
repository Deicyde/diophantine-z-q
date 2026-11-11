---
article_id: af_e51d769c404e3b817b7fc6c9
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.card_compat_even
---

# Maps with a cycle contribute an even number

Let $U,F$ be subsets of a finite set $V$, and let $f$ be a map that moves $U\setminus F$ in $U$
and is not acyclic. Then for every $C\subseteq V$ the number of bijections
$\sigma:U\setminus F\to C$ with $\sigma(i)\in\{i,f(i)\}$ for all $i\in U\setminus F$ is even.

**Proof sketch.** Since $f$ is not acyclic, some point $x$ is periodic and not fixed; let $Z$ be
its forward orbit. No point of $Z$ is fixed, so $Z\subseteq U\setminus F$; $f$ maps $Z$ onto
itself and is injective on $Z$. Let $\sigma$ be compatible. If $\sigma(j)=f(j)$ for some $j\in Z$,
then $\sigma(f(j))\ne f(j)$ by injectivity of $\sigma$, since $f(j)\ne j$; so
$\sigma(f(j))=f(f(j))$, and going around the orbit, $\sigma=f$ on all of $Z$. Hence either
$\sigma(x)=x$ and $\sigma$ is the identity on $Z$, or $\sigma(x)=f(x)$ and $\sigma=f$ on $Z$.
Switching $\sigma$ on $Z$ between the identity and $f$, and keeping it elsewhere, gives again a
compatible bijection onto $C$, because both maps send $Z$ onto $Z$. This switch is an involution of
the compatible bijections without fixed points, since it changes $\sigma(x)$. So their number is
even.

## Depends on

- [Forests on a finite set](forests.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
