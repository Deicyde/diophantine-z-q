---
article_id: af_64179364c84d68b9c69d675b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.card_compat_acyc, ZInQ.RouteK.Rank5b.Sec3.eq_sigmaW
---

# A forest has at most one compatible bijection

Let $U,F,W$ be subsets of a finite set $V$, let $f$ be a forest on $U$ rooted at $F$, and let
$\sigma_W$ and the bijections compatible with $f$ be as in the transversal criterion.

1. Every compatible bijection equals $\sigma_W$.
2. If $F,W\subseteq U$ and $|F|=|W|$, the number of compatible bijections is $1$ if $W$ is a
   transversal of $f$ and $0$ otherwise.

**Proof sketch.** (1) Let $\sigma$ be compatible. By induction on $k$, if $f^k(w)\in U\setminus F$
with $w\in W$, then $\sigma(f^k(w))=f(f^k(w))$. For $k=0$, $\sigma(w)$ lies in $U\setminus W$, so
$\sigma(w)\ne w$. For the step, $f^k(w)$ is in $U\setminus F$ too (otherwise $f$ fixes it), and
$f^{k+1}(w)=\sigma(f^k(w))$ is already the image of another point, so $\sigma$ cannot fix it. In
the other direction, let $i\in U\setminus F$ have $\sigma(i)=f(i)$ without being reached from
$W$. Then $i\notin W$, so $i=\sigma(j)$ for some $j$; $\sigma(j)=j$ is impossible, since then
$j=i$ and $\sigma(i)=i$, so $\sigma(j)=f(j)=i$, and $j$ is not reached from $W$ either. Repeating
this $N=|V|$ times gives a point whose $N$-th iterate is $i$; then $i$ is a root, hence fixed by
$f$, which contradicts $i\in U\setminus F$. So $\sigma=f$ exactly at the points of $U\setminus F$
reached from $W$, that is, $\sigma=\sigma_W$.

(2) By (1) there is at most one compatible bijection, $\sigma_W$, and by the transversal criterion
$\sigma_W$ is one exactly when $W$ is a transversal.

## Depends on

- [Forests on a finite set](forests.md)
- [The map $\sigma_W$ and the transversal criterion](transversal-criterion.md)

## Proof depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
