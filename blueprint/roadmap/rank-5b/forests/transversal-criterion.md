---
article_id: af_b53cd05a37e84a307c04bf24
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.sigmaW_mem_iff, ZInQ.RouteK.Rank5b.Sec3.sigmaW, ZInQ.RouteK.Rank5b.Sec3.merge
---

# The map $\sigma_W$ and the transversal criterion

Let $U,F,W$ be subsets of a finite set $V$ and let $f$ be a forest on $U$ rooted at $F$. Call a
point *reached from $W$* if it is $f^k(w)$ for some $w\in W$ and $k\ge0$, and let $\sigma_W$ be
the map equal to $f$ at the points of $U\setminus F$ reached from $W$ and equal to the identity
elsewhere. Call a bijection $\sigma:U\setminus F\to U\setminus W$ *compatible* with $f$ if
$\sigma(i)\in\{i,f(i)\}$ for all $i\in U\setminus F$.

If $F,W\subseteq U$ and $|F|=|W|$, then $\sigma_W$ is a compatible bijection if and only if $W$ is
a transversal of $f$.

Along the way: consider the conditions (A) no point of $U\setminus F$ reached from $W$ is sent by
$f$ into $W$, and (B) two points of $U\setminus F$ reached from $W$ with the same image under $f$
are equal. If (A) and (B) hold, then no two different points of $W$ have the same root.

**Proof sketch.** Since $|U\setminus F|=|U\setminus W|$, $\sigma_W$ is a compatible bijection if and
only if (A) and (B) hold. Suppose (A) and (B), and let $w\ne w'$ in $W$ have the same root. Take
$f^a(w)=f^b(w')$ with $a+b$ minimal and look at the points just before the meeting point: either
one of them violates (A) or (B), or one of them lies outside $U\setminus F$, is fixed by $f$, and
contradicts the minimality. So the root map is injective on $W$. It sends $W$ into $F$, and
$|W|=|F|$, so every tree contains exactly one point of $W$. Conversely, let $W$ be a transversal.
If $f^k(w)\in U\setminus F$ and $f^{k+1}(w)\in W$, then $f^{k+1}(w)$ and $w$ have the same root, so
$f^{k+1}(w)=w$; then $w$ is periodic, hence fixed, and so is $f^k(w)$, a contradiction; this gives
(A). If $f^a(w)$ and $f^b(w')$ in $U\setminus F$ have the same image, then $w$ and $w'$ have the
same root, so $w=w'$; if $a<b$, then $f^{a+1}(w)$ is periodic, hence fixed, and so is $f^b(w)$, a
contradiction; so $a=b$, which gives (B).

## Depends on

- [Forests on a finite set](forests.md)

## Proof depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
