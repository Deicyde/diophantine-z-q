---
article_id: af_34c5326453dfe22b7d85c310
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.weak_approx_targets, ZInQ.Mult.padicNorm_le_zpow_iff_ap, ZInQ.Mult.exists_crt_idempotent_ap, ZInQ.Mult.padicNorm_div_pow_mul_le_ap
---

# Weak approximation with residue targets

Let $S$ and $S'$ be disjoint finite sets of primes. For $p\in S$ let $m_p\in\mathbb Z$ and
$k_p,n_p\in\mathbb N$. Let $x_0\in\mathbb R$, $\delta>0$ and $X\subset\mathbb R$ finite. Then there
is a nonzero $q\in\mathbb Q$ with $q\notin X$, $|q-x_0|<\delta$,
$$\Bigl|q-\frac{m_p}{p^{k_p}}\Bigr|_p\le p^{-n_p}\quad(p\in S),\qquad v_p(q)\ge0\quad(p\in S').$$

This generalizes the weak approximation used by the original completeness proof, where every
target is $0$: route AP needs $q$ close to a $p$-adic square root of $R_0^{-1}$ at the old
primes where a slope has a pole.

**Proof sketch.** Let $K=\sum_{p\in S}(n_p+k_p)$. By the Chinese remainder theorem choose integers
$E_p\equiv1\pmod{p^K}$ with $E_p\equiv0\pmod{p'^K}$ for the other $p'\in S$, and put
$y=\sum_{p\in S}(m_p/p^{k_p})E_p$; then $|y-m_p/p^{k_p}|_p\le p^{-n_p}$ and $y$ is integral at
$S'$. Weak approximation for the parameter $q$, applied to the target $x_0-y$ with valuations
$\ge K$ on $S$, $\ge0$ on $S'$, and the excluded set $\{-y\}\cup(X-y)$, gives $q'$; take
$q=y+q'$.

## Depends on

None.

## Proof depends on

- [Weak approximation for the parameter $q$](../multiplication/completeness/weak-approximation.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
