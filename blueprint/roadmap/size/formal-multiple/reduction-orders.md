---
article_id: af_da12d4dc3fbbb86f5fa951b7
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.exists_reduction_multiple
---

# Reduction orders of $P_0$

For every integer $N\ge1$ there is an integer $m_0$ with $1\le m_0\le N^6$ such that for
every odd prime $p\mid N$ and every prime $\mathfrak p$ of $\mathbb Z[s]$ containing $p$,
$$[m_0]P_0\in E_1(\mathfrak p),\quad\text{that is, }[m_0]P_0=O\text{ or }v_{\mathfrak p}\bigl(x([m_0]P_0)\bigr)<0 .$$

**Proof sketch.** For each such $\mathfrak p$, $P_0\in E_0(\mathfrak p)$: at $(d)$ by the
bad-place computation, elsewhere by good reduction. Let $n_{\mathfrak p}\ge1$ be the order of
$\operatorname{red}_{\mathfrak p}(P_0)$ in the finite group $\widetilde E_{\rm ns}(k_{\mathfrak p})$;
by the trivial point count $n_{\mathfrak p}\le2|k_{\mathfrak p}|+1$. Put
$$m_0=\prod_{p\mid N,\ p\text{ odd}}\ \prod_{\mathfrak p\ni p}n_{\mathfrak p}.$$
Since $n_{\mathfrak p}\mid m_0$, reduction on the nonsingular part gives
$[m_0]P_0\in E_1(\mathfrak p)$ for every $\mathfrak p$ in the product. For a fixed odd $p$ there
are either two primes with residue fields of $p$ elements or one with $p^2$ elements, so the
inner product is at most $(2p+1)^2\le p^6$ or $2p^2+1\le p^6$. Hence
$m_0\le\prod_{p\mid N}p^6\le N^6$, the last step because the product of the distinct prime
divisors of $N$ divides $N$. For $N=1$, or $N$ a power of $2$, the product is empty and
$m_0=1$.

The manuscript takes the same product of actual reduction orders, bounds the orders at good
places by Hasse ($(p+1)^2<p^3$) and the order at $(d)$ by the order seven of the nonsingular
group of the cusp over $\mathbb F_7$; the trivial count suffices for $m_0\le N^6$.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [Reduction on the nonsingular part](reduction-homomorphism.md)

## Proof depends on

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../../multiplication/local/primes-above-p.md)
- [The trivial point count](trivial-point-count.md)
- [Reduction of $P_0$ at the bad place](bad-place-reduction.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Silverman](../../../sources/size-locators.md#silverman)
