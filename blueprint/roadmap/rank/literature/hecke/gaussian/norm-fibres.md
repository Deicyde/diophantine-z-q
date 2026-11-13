---
article_id: af_edcda516430851cd5bb2eeeb
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.normFiber, ZInQ.Contrib.HeckeFE.mem_normFiber, ZInQ.Contrib.HeckeFE.gmul, ZInQ.Contrib.HeckeFE.toG, ZInQ.Contrib.HeckeFE.norm_toG, ZInQ.Contrib.HeckeFE.toG_gmul, ZInQ.Contrib.HeckeFE.toG_injective, ZInQ.Contrib.HeckeFE.toG_surj, ZInQ.Contrib.HeckeFE.gmul_mem_normFiber, ZInQ.Contrib.HeckeFE.unitsZ, ZInQ.Contrib.HeckeFE.card_unitsZ, ZInQ.Contrib.HeckeFE.normFiber_one, ZInQ.Contrib.HeckeFE.conjZ, ZInQ.Contrib.HeckeFE.toG_conjZ, ZInQ.Contrib.HeckeFE.unitsZ_props, ZInQ.Contrib.HeckeFE.norm_eq_one_cases, ZInQ.Contrib.HeckeFE.isUnit_of_norm_one, ZInQ.Contrib.HeckeFE.unit_mem_unitsZ, ZInQ.Contrib.HeckeFE.norm_unitsZ
---

# Gaussian integers as pairs, norms and units

A pair $(a,b)\in\mathbb Z^2$ stands for the Gaussian integer $a+bi\in\mathbb Z[i]$. The *product* of
pairs is $(a,b)(c,e)=(ac-be,\,ae+bc)$, the *conjugate* of $(a,b)$ is $(a,-b)$, and the *norm* is
$N(a,b)=a^2+b^2$. For a natural number $n$, the *norm fibre* $A_n$ is the finite set of pairs of
norm $n$ (all of them have both coordinates in $[-n,n]$). The *units* are the four pairs
$U=\{(1,0),(-1,0),(0,1),(0,-1)\}$.

1. A pair lies in $A_n$ exactly when its norm is $n$. $U$ has four elements and $A_1=U$.
2. The map $(a,b)\mapsto a+bi$ from $\mathbb Z^2$ to $\mathbb Z[i]$ is a bijection; it carries the
   product of pairs to the product, the conjugate to the complex conjugate, and $N(a,b)$ to the norm
   of $a+bi$.
3. If $\alpha\in A_m$ and $\beta\in A_n$, then $\alpha\beta\in A_{mn}$.
4. For $e\in U$: $e\bar e=1$, $\bar e\in U$, $\bar{\bar e}=e$ and $N(e)=1$.
5. If $a^2+b^2=1$, then $(a,b)\in U$. A Gaussian integer of norm $1$ is a unit of $\mathbb Z[i]$,
   and its pair lies in $U$; the elements of $U$ have norm $1$ in $\mathbb Z[i]$.

**Proof sketch.** (1)–(4) are direct computations; $A_1=U$ by listing the pairs in $[-1,1]^2$.
(5) $a^2+b^2=1$ forces $\{|a|,|b|\}=\{0,1\}$; a Gaussian integer $x$ of norm $1$ satisfies
$x\bar x=1$.

## Depends on

None.

## Sources

- [Arithmetic of the Gaussian integers](../../../../../sources/hecke-locators.md#arithmetic-of-the-gaussian-integers)
